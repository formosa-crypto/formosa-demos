# Disclaimer and Overview

The contents of `map.jazz` are NOT valid Jasmin (yet): this is a proof-of-concept for using higher-order functions in Jasmin.

File `map.jazz` is preprocessed into `map.jpp`, which can be compiled (in this case `amd64`). The assembly is in `map.s`.

File `map.c` provides a simple test case for the defined functions. To build and run the executable, run `make`. The following output is expected:

```
./map
State before map (+1) on 'a' and 'b':
 a: 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1
 b: 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2

State after map (+1) on 'a' and 'b':
 a: 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2
 b: 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3
```

If you have Jasmin available in your system, you can set the variable `JASMIN` (used by the Makefile) and run:
```
make distclean
make
```
