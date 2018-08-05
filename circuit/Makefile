# build against GMP and libsnark of Zcash tree, including linker and g++ flags
# https://github.com/kozyilmaz/zcash-apple.git   Thanx Kazım and libsnark authors
ZC= $(HOME)/zcash/src/zcash-apple

SNARK= $(ZC)/zcash/zcash_v1.1.1/src/snark
GMP= $(ZC)/zcash/zcash_v1.1.1/depends/x86_64-apple-darwin17.5.0
SNARKFLAGS= -fPIC -DBINARY_OUTPUT -DNO_PT_COMPRESSION -fstack-protector-all -std=c++11 -Wall -Wextra -Wno-unused-parameter -Wno-comment -Wfatal-errors -O2 -march=x86-64 -DMONTGOMERY_OUTPUT -DCURVE_ALT_BN128 -DNO_PROCPS -DSTATIC
CPPFLAGS= -g3 -O0 $(SNARKFLAGS) -I$(GMP)/include -I$(SNARK)/libsnark
LIBS= -L$(SNARK) -lsnark -L$(GMP)/lib -lgmpxx -lgmp -lsodium
LDFLAGS= -Wl,-headerpad_max_install_names -Wl,-dead_strip $(LIBS)
CXX= llvm-g++

all:	circuit

.cpp.o:
	llvm-g++ -c -o $@ $(CPPFLAGS) $<

.o:
	llvm-g++ -o $@ $^ $(LDFLAGS) $(LIBS)
