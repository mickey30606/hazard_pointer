all:
	gcc -Wall -o list list.c -lpthread -g -fsanitize=thread
clean:
	rm list
