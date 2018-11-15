set -e
set -o xtrace
/usr/bin/clang pow.cpp -std=c++11 -lstdc++ -o a.out -lisl
./a.out
