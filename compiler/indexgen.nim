#
#
#           The Nimrod Compiler
#        (c) Copyright 2011 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# Generator for input files for source code indexing and cross-reference engines.
# Currently supports:
# CTags
#
# Support wanted for:
# GNU Global(Gtags), CScope, OpenGrok

import 
  os, options, ast, astalgo, msgs, ropes, idents, passes

type 
  TIndexerPass = object of TPassContext
    module*: PSym
    filename*: string
  PIndexerPass = ref TIndexerPass

proc myProcess(c: PPassContext, n: PNode): PNode =
  echo n.kind
  if n.kind == nkProcDef:
    echo n.sons[0].sym.name.s

proc writeCtags* =
  echo "Ctags Wrute"
  var path = options.projectPath

proc myOpen(module: PSym, filename: string): PPassContext =
  echo "Ctags Open"
  var p: PIndexerPass
  new(p)
  p.module = module
  p.filename = filename
  result = p

proc ctagsPass*: TPass =
  initPass(result)
  result.open = myOpen
  result.process = myProcess

