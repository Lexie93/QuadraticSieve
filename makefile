all: mpsiqs.c
	gcc -Wall -Wextra -O2 mpsiqs.c -o mpsiqs.o -lgmp -lm -pthread -pg
