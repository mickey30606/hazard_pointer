/*
 * Hazard pointers are a mechanism for protecting objects in memory from
 * being deleted by other threads while in use. This allows safe lock-free
 * data structures.
 */

#include <assert.h>
#include <inttypes.h>
#include <stdalign.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <threads.h>
#include <limits.h>

#define HP_MAX_THREADS 128
#define HP_MAX_HPS 5 /* This is named 'K' in the HP paper */
#define CLPAD (128 / sizeof(uintptr_t))
#define HP_THRESHOLD_R 8 /* This is named 'R' in the HP paper */

/* Maximum number of retired objects per thread */
#define HP_MAX_RETIRED (HP_MAX_THREADS * HP_MAX_HPS)

#define TID_UNKNOWN -1

#define N_ELEMENTS 128
#define N_THREADS (128 / 2)
#define MAX_THREADS 128

static atomic_uint_fast32_t deletes = 0, inserts = 0;

enum { HP_NEXT = 2, HP_CURR = 1, HP_PREV = 0 };

#define is_marked(p) (bool) ((uintptr_t)(p) &0x01)
#define get_marked(p) ((uintptr_t)(p) | (0x01))
#define get_unmarked(p) ((uintptr_t)(p) & (~0x01))

#define get_marked_node(p) ((list_node_t *) get_marked(p))
#define get_unmarked_node(p) ((list_node_t *) get_unmarked(p))

#ifdef ANALYZE

typedef struct anal_ins_del {
    bool is_insert;
    long int success;
    long int search_again;
    long int failed;
} anal_ins_del_t;

typedef struct anal_find {
    long int travels;
    long int after_retire;
    long int go_retire;
    long int go_retire_and_try_again;
    long int find_try_again;
} anal_find_t;

typedef struct anal_retire {
    long int retire_success;
    long int retire_failed;
}anal_retire_t;

typedef struct anal_atm_ops{
    long int atomic_load;
    long int atomic_store;
    long int compare_and_swap;
}anal_atm_ops_t;

enum{
    OUT_SIDE_WHILE = 0,
    NEXT_PROTECT_FAILED,
    DEL_MARKED_FAILED
};

enum{
    RETIRE_TRACE_success=1,
    RETIRE_TRACE_failed=2
};

anal_ins_del_t analyze_ins_del[MAX_THREADS] = {0};
anal_find_t analyze_find[MAX_THREADS] = {0};
anal_retire_t analyze_retire[MAX_THREADS] = {0};
anal_atm_ops_t analyze_atm_ops[MAX_THREADS] = {0};

#define INIT(insert, tid) ({ analyze_ins_del[tid].is_insert = insert; })

#define CAS(obj, expected, desired)\
    ({\
        bool __ret = atomic_compare_exchange_strong(obj, expected, desired);\
        analyze_atm_ops[tid()].compare_and_swap += 1;\
        __ret;\
     })

#define ATOMIC_LOAD(obj)\
    ({\
        analyze_atm_ops[tid()].atomic_load += 1;\
        atomic_load(obj);\
     })

#define ATOMIC_STORE_EXPLICIT(obj, desired, order)\
    do{\
        analyze_atm_ops[tid()].atomic_store += 1;\
        atomic_store_explicit(obj, desired, order);\
    }while(0);

#define TRAVEL(tid) ({analyze_find[tid].travels += 1;})

#define SEARCH_AGAIN(tid) ({ analyze_ins_del[tid].search_again += 1; })

#define HELP_RETIRE(tid)\
({\
    analyze_find[tid].go_retire += 1; \
    analyze_find[tid].after_retire = 2;\
})

#define KEEP_GOING(tid)\
({\
 if(analyze_find[tid].after_retire){\
    analyze_find[tid].after_retire -= 1;\
 }\
})

#define GOTO_TRY_AGAIN(tid, state)\
({\
    analyze_find[tid].find_try_again += 1;\
    if(analyze_find[tid].after_retire){\
        if(state != OUT_SIDE_WHILE){\
            analyze_find[tid].go_retire_and_try_again += 1;\
        }\
        analyze_find[tid].after_retire = 0;\
    }\
    goto try_again;\
})

#define SUCCESS(tid) ({ analyze_ins_del[tid].success += 1; })

#define FAILED(tid) ({ analyze_ins_del[tid].failed += 1; })

#define RETIRE_TRACE(tid,state)\
    ({\
        if(RETIRE_TRACE_##state){\
            analyze_retire[tid].retire_##state += 1;\
        }\
     })

static void analyze_print(void){
    anal_ins_del_t *insert, *delete;
    insert = calloc(1, sizeof(anal_ins_del_t));
    delete = calloc(1, sizeof(anal_ins_del_t));
    insert->is_insert = 1;

#define ANAL_INS_DEL_SUM(is_insert, ops, i)\
    ({\
        if(is_insert){\
            insert->ops += analyze_ins_del[i].ops;\
        }else{\
            delete->ops += analyze_ins_del[i].ops;\
        }\
     })

#define ANAL_FIND_SUM(ops, i)\
    ({\
        if(i){\
            analyze_find[0].ops += analyze_find[i].ops;\
        }\
     })

#define ANAL_RETIRE_SUM(ops, i)\
    ({\
        if(i){\
            analyze_retire[0].ops += analyze_retire[i].ops;\
        }\
     })

#define ANAL_ATM_OPS_SUM(ops, i)\
    ({\
        if(i){\
            analyze_atm_ops[0].ops += analyze_atm_ops[i].ops;\
        }\
     })
    for(int i=0;i<MAX_THREADS;i++){
        ANAL_INS_DEL_SUM(analyze_ins_del[i].is_insert, success, i);
        ANAL_INS_DEL_SUM(analyze_ins_del[i].is_insert, failed, i);
        ANAL_INS_DEL_SUM(analyze_ins_del[i].is_insert, search_again, i);
        ANAL_FIND_SUM(find_try_again, i);
        ANAL_FIND_SUM(go_retire, i);
        ANAL_FIND_SUM(travels, i);
        ANAL_FIND_SUM(go_retire_and_try_again, i);
        ANAL_RETIRE_SUM(retire_success, i);
        ANAL_RETIRE_SUM(retire_failed, i);
        ANAL_ATM_OPS_SUM(atomic_load, i);
        ANAL_ATM_OPS_SUM(atomic_store, i);
        ANAL_ATM_OPS_SUM(compare_and_swap, i);
    }

#undef ANAL_ATM_OPS_SUM
#undef ANAL_INS_DEL_SUM
#undef ANAL_FIND_SUM
#undef ANAL_RETIRE_SUM

    printf("\nlist_insert() and list_delete()\n\n");
    printf("%-30s%-20s/%20s\n", "", "insert", "delete");
#define PRINT_ANAL(ops) printf("%-30s%-20ld/%20ld\n", #ops, insert->ops, delete->ops);
    PRINT_ANAL(success);
    PRINT_ANAL(failed);
    PRINT_ANAL(search_again);
#undef PRINT_ANAL
    for(int i=0;i<71;i++){
        printf("=");
    }

    printf("\n__list_find()\n\n");
#define PRINT_ANAL(ops) printf("%-30s%-20ld\n", #ops, analyze_find[0].ops);
    PRINT_ANAL(travels);
    PRINT_ANAL(find_try_again);
    PRINT_ANAL(go_retire);
    PRINT_ANAL(go_retire_and_try_again);
#undef PRINT_ANAL

    for(int i=0;i<71;i++){
        printf("=");
    }
    printf("\nhp_retire()\n\n");
#define PRINT_ANAL(ops) printf("%-30s%-20ld\n", #ops, analyze_retire[0].ops);
    PRINT_ANAL(retire_success);
    PRINT_ANAL(retire_failed);
#undef PRINT_ANAL
    for(int i=0;i<71;i++){
        printf("=");
    }
    printf("\natomic operations\n\n");
#define PRINT_ANAL(ops) printf("%-30s%-20ld\n", #ops, analyze_atm_ops[0].ops);
    PRINT_ANAL(atomic_load);
    PRINT_ANAL(atomic_store);
    PRINT_ANAL(compare_and_swap);
}

#define ANALYZE_INIT atexit(analyze_print)

#else

#define INIT(insert, tid) ({})

#define CAS(obj, expected, desired)\
    ({\
        bool __ret = atomic_compare_exchange_strong(obj, expected, desired);\
        __ret;\
     })

#define ATOMIC_LOAD(obj)\
    ({\
        atomic_load(obj);\
     })

#define ATOMIC_STORE_EXPLICIT(obj, desired, order)\
    do{\
        atomic_store_explicit(obj, desired, order);\
    }while(0);

#define TRAVEL(tid) ({})

#define SEARCH_AGAIN(tid) ({})

#define GOTO_TRY_AGAIN(tid, state) ({ goto try_again; })

#define KEEP_GOING(tid) ({})

#define HELP_RETIRE(tid) ({})

#define SUCCESS(tid) ({})

#define FAILED

#define RETIRE_TRACE(tid,state) ({})

static void analyze_print(void){}

#define ANALYZE_INIT atexit(analyze_print)

#endif

typedef struct {
    int size;
    uintptr_t *list;
} retirelist_t;

typedef struct list_hp list_hp_t;
typedef void(list_hp_deletefunc_t)(void *);

struct list_hp {
    int max_hps;
    alignas(128) atomic_uintptr_t *hp[HP_MAX_THREADS];
    alignas(128) retirelist_t *rl[HP_MAX_THREADS * CLPAD];
    list_hp_deletefunc_t *deletefunc;
};

static thread_local int tid_v = TID_UNKNOWN;
static atomic_int_fast32_t tid_v_base = ATOMIC_VAR_INIT(0);
static inline int tid(void)
{
    if (tid_v == TID_UNKNOWN) {
        tid_v = atomic_fetch_add(&tid_v_base, 1);
        assert(tid_v < HP_MAX_THREADS);
    }
    return tid_v;
}

/* Create a new hazard pointer array of size 'max_hps' (or a reasonable
 * default value if 'max_hps' is 0). The function 'deletefunc' will be
 * used to delete objects protected by hazard pointers when it becomes
 * safe to retire them.
 */
list_hp_t *list_hp_new(size_t max_hps, list_hp_deletefunc_t *deletefunc)
{
    list_hp_t *hp = aligned_alloc(128, sizeof(*hp));
    assert(hp);

    if (max_hps == 0)
        max_hps = HP_MAX_HPS;

    *hp = (list_hp_t){.max_hps = max_hps, .deletefunc = deletefunc};

    for (int i = 0; i < HP_MAX_THREADS; i++) {
        hp->hp[i] = calloc(CLPAD * 2, sizeof(hp->hp[i][0]));
        hp->rl[i * CLPAD] = calloc(1, sizeof(*hp->rl[0]));
        for (int j = 0; j < hp->max_hps; j++)
            atomic_init(&hp->hp[i][j], 0);
        hp->rl[i * CLPAD]->list = calloc(HP_MAX_RETIRED, sizeof(uintptr_t));
    }

    return hp;
}

/* Destroy a hazard pointer array and clean up all objects protected
 * by hazard pointers.
 */
void list_hp_destroy(list_hp_t *hp)
{
    long int num = 0;
    for (int i = 0; i < HP_MAX_THREADS; i++) {
        free(hp->hp[i]);
        retirelist_t *rl = hp->rl[i * CLPAD];
        num += rl->size;
        for (int j = 0; j < rl->size; j++) {
            void *data = (void *) rl->list[j];
            hp->deletefunc(data);
        }
        free(rl->list);
        free(rl);
    }
    free(hp);
    fprintf(stderr, "still in retire list = %ld\n", num);

}

/* Clear all hazard pointers in the array for the current thread.
 * Progress condition: wait-free bounded (by max_hps)
 */
void list_hp_clear(list_hp_t *hp)
{
    for (int i = 0; i < hp->max_hps; i++)
        atomic_store_explicit(&hp->hp[tid()][i], 0, memory_order_release);
}

/* This returns the same value that is passed as ptr.
 * Progress condition: wait-free population oblivious.
 */
uintptr_t list_hp_protect_ptr(list_hp_t *hp, int ihp, uintptr_t ptr)
{
    atomic_store(&hp->hp[tid()][ihp], ptr);
    return ptr;
}

/* Same as list_hp_protect_ptr(), but explicitly uses memory_order_release.
 * Progress condition: wait-free population oblivious.
 */
uintptr_t list_hp_protect_release(list_hp_t *hp, int ihp, uintptr_t ptr)
{
    atomic_store_explicit(&hp->hp[tid()][ihp], ptr, memory_order_release);
    return ptr;
}

int comp(const void *a, const void *b){
    return *(uintptr_t *)a < *(uintptr_t *)b;
}

/* Retire an object that is no longer in use by any thread, calling
 * the delete function that was specified in list_hp_new().
 *
 * Progress condition: wait-free bounded (by the number of threads squared)
 */
void list_hp_retire(list_hp_t *hp, uintptr_t ptr)
{
    retirelist_t *rl = hp->rl[tid() * CLPAD];
    rl->list[rl->size++] = ptr;
    assert(rl->size < HP_MAX_RETIRED);

    if (rl->size < HP_THRESHOLD_R)
        return;

    uintptr_t *hazard_pointer = calloc(HP_MAX_THREADS*HP_MAX_HPS, sizeof(uintptr_t));
    size_t hp_size = 0;
    bool can_delete = true;

    for(int itid=0; itid < HP_MAX_THREADS; itid++){
        for(int ihp=1;ihp >=0; ihp--){
            uintptr_t tmp = atomic_load(&hp->hp[itid][ihp]);
            if(tmp){
                hazard_pointer[hp_size++] = tmp;
            }
        }
    }

    qsort(hazard_pointer, hp_size, sizeof(uintptr_t), comp);

    for(size_t iret=0; iret < rl->size; iret++){
        uintptr_t obj = rl->list[iret];
        long int middle, right = hp_size-1, left = 0;
        while(left <= right){
            middle = (right + left)/2;
            if(hazard_pointer[middle] > obj){
                left = middle + 1;
            }else if(hazard_pointer[middle] < obj){
                right = middle -1;
            }else{
                can_delete = false;
                break;
            }
        }
        if(can_delete){
            size_t bytes = (rl->size - iret) * sizeof(rl->list[0]);
            memmove(&rl->list[iret], &rl->list[iret + 1], bytes);
            rl->size--;
            hp->deletefunc((void*) obj);
            RETIRE_TRACE(tid(), success);
        }else{
            RETIRE_TRACE(tid(), failed);
        }
    }

    free(hazard_pointer);
}

#include <pthread.h>


typedef uintptr_t list_key_t;

typedef struct list_node {
    alignas(128) uint32_t magic;
    alignas(128) atomic_uintptr_t next;
    list_key_t key;
} list_node_t;

/* Per list variables */

typedef struct list {
    atomic_uintptr_t head, tail;
    list_hp_t *hp;
} list_t;


#define LIST_MAGIC (0xDEADBEAF)

list_node_t *list_node_new(list_key_t key)
{
    list_node_t *node = aligned_alloc(128, sizeof(*node));
    assert(node);
    *node = (list_node_t){.magic = LIST_MAGIC, .key = key};
    (void) atomic_fetch_add(&inserts, 1);
    return node;
}

void list_node_destroy(list_node_t *node)
{
    if (!node)
        return;
    assert(node->magic == LIST_MAGIC);
    free(node);
    (void) atomic_fetch_add(&deletes, 1);
}

static void __list_node_delete(void *arg)
{
    list_node_t *node = (list_node_t *) arg;
    list_node_destroy(node);
}

static bool __list_find(list_t *list,
                        list_key_t *key,
                        atomic_uintptr_t **par_prev,
                        list_node_t **par_curr,
                        list_node_t **par_next)
{
    atomic_uintptr_t *prev = NULL;
    list_node_t *curr = NULL, *next = NULL;

try_again:
    prev = &list->head;
    curr = (list_node_t *) ATOMIC_LOAD(prev);
    (void) list_hp_protect_ptr(list->hp, HP_CURR, (uintptr_t) curr);
    if (atomic_load(prev) != get_unmarked(curr))
        GOTO_TRY_AGAIN(tid(), OUT_SIDE_WHILE);
    while (true) {
        TRAVEL(tid());
        KEEP_GOING(tid());
        next = (list_node_t *) ATOMIC_LOAD(&get_unmarked_node(curr)->next);
        /* On a CAS failure, the search function, "__list_find," will simply
         * have to go backwards in the list until an unmarked element is found
         * from which the search in increasing key order can be started.
         */
        if (atomic_load(prev) != get_unmarked(curr))
            GOTO_TRY_AGAIN(tid(), NEXT_PROTECT_FAILED);
        if (get_unmarked_node(next) == next) {
            if (!(get_unmarked_node(curr)->key < *key)) {
                *par_curr = curr;
                *par_prev = prev;
                *par_next = next;
                return (get_unmarked_node(curr)->key == *key);
            }
            prev = &get_unmarked_node(curr)->next;
            (void) list_hp_protect_release(list->hp, HP_PREV,
                                           get_unmarked(curr));
        } else {
            uintptr_t tmp = get_unmarked(curr);
            if (!CAS(prev, &tmp, get_unmarked(next)))
                GOTO_TRY_AGAIN(tid(), DEL_MARKED_FAILED);
            list_hp_retire(list->hp, get_unmarked(curr));
            HELP_RETIRE(tid());
        }
		curr = (list_node_t *) ATOMIC_LOAD(prev);
		(void) list_hp_protect_ptr(list->hp, HP_CURR, (uintptr_t) curr);
		if (atomic_load(prev) != get_unmarked(curr))
			GOTO_TRY_AGAIN(tid(), OUT_SIDE_WHILE);
    }
}

bool list_insert(list_t *list, list_key_t key)
{
    list_node_t *curr = NULL, *next = NULL;
    atomic_uintptr_t *prev = NULL;

    list_node_t *node = list_node_new(key);

    while (true) {
        if (__list_find(list, &key, &prev, &curr, &next)) {
            list_node_destroy(node);
            list_hp_clear(list->hp);
            FAILED(tid());
            return false;
        }
        ATOMIC_STORE_EXPLICIT(&node->next, (uintptr_t) curr,
                              memory_order_relaxed);
        uintptr_t tmp = get_unmarked(curr);
        if (CAS(prev, &tmp, (uintptr_t) node)) {
            list_hp_clear(list->hp);
            SUCCESS(tid());
            return true;
        }
        SEARCH_AGAIN(tid());
    }
}

bool list_delete(list_t *list, list_key_t key)
{
    list_node_t *curr, *next;
    atomic_uintptr_t *prev;
    while (true) {
        if (!__list_find(list, &key, &prev, &curr, &next)) {
            list_hp_clear(list->hp);
            FAILED(tid());
            return false;
        }

        uintptr_t tmp = get_unmarked(next);

        if (!CAS(&curr->next, &tmp,
                    get_marked(next))){

            SEARCH_AGAIN(tid());
            continue;
        }

        tmp = get_unmarked(curr);
        if (CAS(prev, &tmp, get_unmarked(next))) {
            list_hp_clear(list->hp);
            list_hp_retire(list->hp, get_unmarked(curr));
        } else {
            list_hp_clear(list->hp);
        }
        SUCCESS(tid());
        return true;
    }
}

list_t *list_new(void)
{
    list_t *list = calloc(1, sizeof(*list));
    assert(list);
    list_node_t *head = list_node_new(0), *tail = list_node_new(UINTPTR_MAX);
    assert(head), assert(tail);
    list_hp_t *hp = list_hp_new(3, __list_node_delete);

    atomic_init(&head->next, (uintptr_t) tail);
    *list = (list_t){.hp = hp};
    atomic_init(&list->head, (uintptr_t) head);
    atomic_init(&list->tail, (uintptr_t) tail);

    return list;
}

void list_destroy(list_t *list)
{
    assert(list);
    list_node_t *prev = (list_node_t *) atomic_load(&list->head);
    list_node_t *node = (list_node_t *) atomic_load(&prev->next);
    uintptr_t tmp = prev->key;
    long int num = 1;
    bool check_order = true;
    while (node) {
        num++;
        list_node_destroy(prev);
        prev = node;
        node = (list_node_t *) atomic_load(&prev->next);
        if(tmp >= prev->key){
            check_order = false;
        }
        tmp = prev->key;
    }
    if(check_order){
        fprintf(stderr, "list is ordered with %ld node\n", num);
    }else{
        fprintf(stderr, "list is not ordered!!! with %ld node\n", num);
    }
    list_node_destroy(prev);
    list_hp_destroy(list->hp);
    free(list);
}

static uintptr_t elements[MAX_THREADS + 1][N_ELEMENTS];
static thread_local int distribute_insert = TID_UNKNOWN;
static thread_local int distribute_delete = TID_UNKNOWN;
static atomic_int_fast32_t distrubute_base_insert = ATOMIC_VAR_INIT(0);
static atomic_int_fast32_t distrubute_base_delete = ATOMIC_VAR_INIT(0);

int distribute_insert_f(void){
	if(distribute_insert == TID_UNKNOWN){
		distribute_insert = atomic_fetch_add(&distrubute_base_insert, 1);
	}
	return distribute_insert;
}

int distribute_delete_f(void){
	if(distribute_delete == TID_UNKNOWN){
		distribute_delete = atomic_fetch_add(&distrubute_base_delete, 1);
	}
	return distribute_delete;
}


static void *insert_thread(void *arg)
{
    list_t *list = (list_t *) arg;

    INIT(true, tid());

    for (size_t i = 0; i < N_ELEMENTS; i++)
        (void) list_insert(list, (uintptr_t) &elements[distribute_insert_f()][i]);
    return NULL;
}

static void *delete_thread(void *arg)
{
    list_t *list = (list_t *) arg;

    INIT(false, tid());

    for (size_t i = 0; i < N_ELEMENTS; i++)
        (void) list_delete(list, (uintptr_t) &elements[distribute_delete_f()][i]);
    return NULL;
}

int main(void)
{
    ANALYZE_INIT;
    list_t *list = list_new();

    pthread_t thr[N_THREADS];

    int k = 16;
    int m = 16+k;

    INIT(true, tid());
    for(size_t j = 0; j< 8;j++){
        for(size_t i = 0;i<N_ELEMENTS;i++){
            list_insert(list, (uintptr_t) &elements[j][i]);
        }
    }
    for(size_t i = 0;i<k;i++){
        pthread_create(&thr[i], NULL, delete_thread, list);
    }
    for(size_t i = k;i<m;i++){
        pthread_create(&thr[i], NULL, insert_thread, list);
    }

    for (size_t i = 0; i < m; i++)
        pthread_join(thr[i], NULL);

    list_destroy(list);

    fprintf(stderr, "inserts = %zu, deletes = %zu\n", atomic_load(&inserts),
            atomic_load(&deletes));

    return 0;
}
