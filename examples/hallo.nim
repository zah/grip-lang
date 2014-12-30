type
  Foo[N: static[int]] = object
 
proc foobar[N](foo: Foo[N]) =
  var x = $N
  echo(x)
 
var f: Foo[3]
f.foobar
