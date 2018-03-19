#
#
#            Nim's Runtime Library
#        (c) Copyright 2017 Nim Authors
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.

## This module implements types and macros for writing asynchronous code
## for the JS backend. It provides tools for interaction with JavaScript async API-s
## and libraries, writing async procedures in Nim and converting callback-based code
## to promises.
##
## A Nim procedure is asynchronous when it includes the ``{.async.}`` pragma. It
## should always have a ``Future[T]`` return type or not have a return type at all.
## A ``Future[void]`` return type is assumed by default.
##
## This is roughly equivalent to the ``async`` keyword in JavaScript code.
##
## .. code-block:: nim
##  proc loadGame(name: string): Future[Game] {.async.} =
##    # code
##
## should be equivalent to
##
## .. code-block:: javascript
##   async function loadGame(name) {
##     // code
##   }
##
## A call to an asynchronous procedure usually needs ``await`` to wait for
## the completion of the ``Future``.
##
## .. code-block:: nim
##   var game = await loadGame(name)
##
## Often, you might work with callback-based API-s. You can wrap them with
## asynchronous procedures using promises and ``newPromise``:
##
## .. code-block:: nim
##   proc loadGame(name: string): Future[Game] =
##     var promise = newPromise() do (resolve: proc(response: Game)):
##       cbBasedLoadGame(name) do (game: Game):
##         resolve(game)
##     return promise
##
## Forward definitions work properly, you just need to always add the ``{.async.}`` pragma:
##
## .. code-block:: nim
##   proc loadGame(name: string): Future[Game] {.async.}
##
## JavaScript compatibility
## ~~~~~~~~~~~~~~~~~~~~~~~~~
##
## Nim currently generates `async/await` JavaScript code which is supported in modern
## EcmaScript and most modern versions of browsers, Node.js and Electron.
## If you need to use this module with older versions of JavaScript, you can
## use a tool that backports the resulting JavaScript code, as babel.

import jsffi
import macros

when not defined(js) and not defined(nimdoc) and not defined(nimsuggest):
  {.fatal: "Module asyncjs is designed to be used with the JavaScript backend.".}

type
  Future*[T] = ref object
    future*: T
  ## Wraps the return type of an asynchronous procedure.

  PromiseJs* {.importcpp: "Promise".} = ref object
  ## A JavaScript Promise


proc replaceReturn(node: var NimNode) =
  var z = 0
  for s in node:
    var son = node[z]
    let jsResolve = ident("jsResolve")
    if son.kind == nnkReturnStmt:
      let value = if son[0].kind != nnkEmpty: nnkCall.newTree(jsResolve, son[0]) else: jsResolve
      node[z] = nnkReturnStmt.newTree(value)
    elif son.kind == nnkAsgn and son[0].kind == nnkIdent and $son[0] == "result":
      node[z] = nnkAsgn.newTree(son[0], nnkCall.newTree(jsResolve, son[1]))
    else:
      replaceReturn(son)
    inc z

proc isFutureVoid(node: NimNode): bool =
  result = node.kind == nnkBracketExpr and
           node[0].kind == nnkIdent and $node[0] == "Future" and
           node[1].kind == nnkIdent and $node[1] == "void"

proc generateJsasync(arg: NimNode): NimNode =
  assert arg.kind == nnkProcDef
  result = arg
  var isVoid = false
  let jsResolve = ident("jsResolve")
  if arg.params[0].kind == nnkEmpty:
    result.params[0] = nnkBracketExpr.newTree(ident("Future"), ident("void"))
    isVoid = true
  elif isFutureVoid(arg.params[0]):
    isVoid = true

  var code = result.body
  replaceReturn(code)
  result.body = nnkStmtList.newTree()

  if len(code) > 0:
    var awaitFunction = quote:
      proc await[T](f: Future[T]): T {.importcpp: "(await #)".}
    result.body.add(awaitFunction)

    var resolve: NimNode
    if isVoid:
      resolve = quote:
        var `jsResolve` {.importcpp: "undefined".}: Future[void]
    else:
      resolve = quote:
        proc jsResolve[T](a: T): Future[T] {.importcpp: "#".}
    result.body.add(resolve)
  else:
    result.body = newEmptyNode()
  for child in code:
    result.body.add(child)

  if len(code) > 0 and isVoid:
    var voidFix = quote:
      return `jsResolve`
    result.body.add(voidFix)

  let asyncPragma = quote:
    {.codegenDecl: "async function $2($3)".}

  result.addPragma(asyncPragma[0])

macro async*(arg: untyped): untyped =
  ## Macro which converts normal procedures into
  ## javascript-compatible async procedures
  generateJsasync(arg)

proc newPromise*[T](handler: proc(resolve: proc(response: T))): Future[T] {.importcpp: "(new Promise(#))".}
  ## A helper for wrapping callback-based functions
  ## into promises and async procedures

proc newPromise*(handler: proc(resolve: proc())): Future[void] {.importcpp: "(new Promise(#))".}
  ## A helper for wrapping callback-based functions
  ## into promises and async procedures
