#!/bin/sh
set -eux

export PATH="`${LLVM_CONFIG:-llvm-config-mp-8.0} --bindir`:$PATH"

clean () {
	cd ./xed
	./mfile.py clean
	cd ..

	rm -Rf libxed
}

build () {
	cd ./xed
	# Need to set ia32 or else mbuild adds -m64
	patch -Np1 < ../xed.patch || true
	./mfile.py --host-cpu=ia32 --host-os=lin --extra-flags="-Oz -emit-llvm -target le32-unknown-nacl -nostdlibinc -isystem ../pdclib/include -isystem ../pdclib_platform/include"
	cd ..
	
	rm -Rf build/libxed
	mkdir -p build/libxed
	cd build/libxed
	ar x ../../xed/obj/libxed.a
	cd ../..

	rm -Rf build/libc
	mkdir -p build/libc
	cd build/libc
	for file in \
		../../pdclib/functions/*/*.c \
		../../pdclib_platform/functions/*/*.c \
	; do
		case $file in
			../../pdclib/functions/_dlmalloc/*) continue;;
		esac
		clang -Oz -emit-llvm -target le32-unknown-nacl -nostdlibinc -isystem ../../pdclib/include -isystem ../../pdclib_platform/include $file -c -o "`basename "$file" .c`.o"
	done
	cd ../..
}

case "${1-}" in
	clean) clean ;;
	build) build ;;
	'') build ;;
	*) echo 'Specify "build" or "clean"' >&2 ;;
esac
