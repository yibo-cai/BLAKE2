PROG=b2sum
PREFIX?=/usr/local
MANDIR?=$(PREFIX)/man
NO_OPENMP?=0
NO_OPENMP_0=-fopenmp
NO_OPENMP_1=
CC?=gcc
CFLAGS?=-O3 -march=native
CFLAGS+=-std=c99 -Wall -Wextra -pedantic -Wno-long-long -I../sse
CFLAGS+=$(NO_OPENMP_$(NO_OPENMP))
LIBS=
FILES=b2sum.c ../ref/blake2b-ref.c ../ref/blake2s-ref.c
#FILES=b2sum.c ../neon/blake2b.c ../neon/blake2s.c
all: $(FILES)
	$(CC) $(FILES) $(CFLAGS) $(LIBS) -o $(PROG)

clean:
	rm -f $(PROG)

install:
	install -d $(DESTDIR)$(PREFIX)/bin
	install -d $(DESTDIR)$(MANDIR)/man1
	install -m 755 $(PROG) $(DESTDIR)$(PREFIX)/bin
	install -m 644 b2sum.1 $(DESTDIR)$(MANDIR)/man1/$(PROG).1
