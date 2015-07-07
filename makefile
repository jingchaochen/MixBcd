CC=gcc
CFLAGS= -Wall -Wextra -static -O3 -funroll-loops -fexpensive-optimizations 

all: MixBcd

MixBcd: MixBcd.c
	$(CC) $(CFLAGS)  MixBcd.c -lm -o MixBcd
clean:	
	rm -f *.o *.a *.so
	rm -f MixBcd 

