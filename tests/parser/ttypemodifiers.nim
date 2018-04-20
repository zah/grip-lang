import macros

dumpTree:
  type 
    X = ptr[int]
    P = ptr
    S = static
    T = type
 
  proc foo(a: type,
           b: type[int],
           c: type int,
           z: type(int),
           p: type(a),
           d: type tuple,
           e: static,
           f: static[int],
           g: static int,
           r: ref,
           w: ref (int),
           m: ref[int],
           n: ref int): type =
    echo x

