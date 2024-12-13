# JITxpr
A JIT-compiled infix evaluator

# Installation
1. Install [GNU Lightning](https://www.gnu.org/software/lightning/)
2. Run build script
```bash
./build.sh
```
OR
```bash
g++ eval.cpp -Ofast -Wall -Wextra -o ex -llightning && ./ex
```

## TODO:
1. Remove '(' and ')' from RPN output
2. remove dead code
3. error handling and srp for jit instance
4. Add support for binding and other datatypes


