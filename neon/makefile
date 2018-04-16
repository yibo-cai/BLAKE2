CC=gcc
CFLAGS=-O3 -I../testvectors -Wall -Wextra -std=c89 -pedantic -Wno-long-long
BLAKEBINS=blake2b

all:		$(BLAKEBINS) check

blake2b:	blake2b.c
		$(CC) blake2b.c -o $@ $(CFLAGS) -DBLAKE2B_SELFTEST

check:      blake2b
	        ./blake2b

clean:
		rm -rf *.o genkat-c genkat-json blake2-kat.h blake2-kat.json $(BLAKEBINS)
