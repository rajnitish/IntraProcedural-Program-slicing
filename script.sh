clear
cd build
cmake .. && make && cd ../test && clang -Xclang -load -Xclang ../build/libInPSPass.so -c example.c

#clang -O0 -S -emit-llvm example.c -o example.ll

#cc -no-pie example.o
#./a.out
