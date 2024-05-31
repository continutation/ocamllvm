LLVM_CONFIG?=llvm-config-mp-8.0

export PATH:=$(shell $(LLVM_CONFIG) --bindir):$(PATH)

_:=$(shell test -d build || ./build.sh)

.PHONY: all clean

all: build/combined.bc

clean:
	touch build/_.bc build/_.ll
	rm -Rf build/*.bc build/*.ll

# We use le32-unknown-nacl because otherwise clang generates some ABI-specific code,
# such as a lowered va_list implementation. We don't really handle any real "ABI" beyond
# little-endian memory.
MYFLAGS:=-emit-llvm -target le32-unknown-nacl -Oz -nostdlibinc -isystem pdclib/include -isystem pdclib_platform/include

build/xed-ex1.bc: xed/examples/xed-ex1.c
	clang $(MYFLAGS) -Ixed/include/public -Ixed/include/public/xed -Ixed/include/private -Ixed/obj -Ixed/obj/include-private $^ -c -o $@

build/xed-examples-util.bc: xed/examples/xed-examples-util.c
	clang $(MYFLAGS) -Ixed/include/public -Ixed/include/public/xed -Ixed/include/private -Ixed/obj -Ixed/obj/include-private $^ -c -o $@

build/%.bc: %.c
	clang $(MYFLAGS) $^ -c -o $@

build/%.bc: %.cpp
	clang++ $(MYFLAGS) $^ -c -o $@

build/combined.bc: $(wildcard build/libxed/*.o) $(wildcard build/libc/*.o) build/xed-ex1.bc build/xed-examples-util.bc
	llvm-link $^ | opt -name-anon-globals -instnamer -internalize -internalize-public-api-list=main -argpromotion -loweratomic -lowerinvoke -Oz -o $@
