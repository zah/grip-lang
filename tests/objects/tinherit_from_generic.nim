discard """
  output: '''true BaseObj[int]'''
"""

import typetraits

# bug #4673
type
  BaseObj[T] = ref object of RootObj
  SomeObj = ref object of BaseObj[int]

proc doSomething[T](o: BaseObj[T]) =
  echo "true ", o.type.name

var o = new(SomeObj)
o.doSomething() # Error: cannot instantiate: 'T'
