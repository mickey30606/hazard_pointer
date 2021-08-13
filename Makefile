all:
	gcc -Wall -o list list.c -lpthread -g
analyze:
	gcc -Wall -D ANALYZE -o list list.c -lpthread -g -fsanitize=thread
clean:
	rm list
