import
  passes, ast, llstream, msgs, idents, sem, semdata, cgen, transf,
  strutils, astalgo, wordrecg

type
  TPassData = tuple[input: PNode, closeOutput: Pnode]
  TIndentMode = enum Tabs, Spaces, Unknown

  TLines = seq[string]
  TGripFile = object
    fileIdx: int32
    lines: TLines # consider gap buffers for these
    indents: seq[int]
    indentMode: TIndentMode
    pos: TPos
    bounds: TPos
    breakCall: bool
    pendingOp: TPrecedence

  PGripFile = ref TGripFile

  TPrecedence = tuple[id: PNode, opdat: TOpData, before, after: TWhiteSpace]

  TShuntingYardStack = object
    opStack: array[0..1024, TPrecedence]
    opStackTop: int
    expStack: array[0..1024, PNode]
    expStackTop: int

  TOpFlag = enum
    Left,
    Right,
    Prefix,
    Infix,
    Postfix,
    CallBreaker,
    Unary,

  TOpFlags = set[TOpFlag]

  TOpData = object
    precedence: int
    flags: TOpFlags

  TWhiteSpace = tuple[spaces, tabs, newlines: int]

const
  IDStartChars = { 'a'..'z', 'A'..'Z' }
  IDChars = { 'a'..'z', 'A'..'Z', '0'..'9' }
  NumStartChars = { '0'..'9' }
  NumChars = { '0'..'9', '.' }
  StrStartChars = { '\'', '\"' }
  CharsWS = {' ', '\t'}
  OpChars = { ':', '=', '.', ';', ',', '~', '@', '#', '$', '\\',
              '<', '>', '&', '|', '!', '?', '%', '^', '+', '-', '*', '/' }

  EOF = '\0'

var gGripFiles: seq[PGripFile] = @[]

proc getOp(id: PIdent): TOpData =
  template ret(prec, f: expr): stmt =
    result.precedence = 220 - prec
    result.flags = f
    # result.flags = flags

  case id.s
  of ";":
    ret(50, {Left, Infix, CallBreaker})
  of "=", "+=", "-=", "*=", "/=", "%=", "<<=", ">>=", "^=", "&=":
    ret(60, {Left, Infix, CallBreaker})
  of "if", "unless", "while", "for":
    ret(70, {Right, Infix, CallBreaker})
  of "else":
    ret(80, {Left, Infix, CallBreaker})
  of "|", "|>", "=>", "->":
    ret(110, {Left, Infix, CallBreaker})
  of "<|":
    ret(110, {Right, Infix, CallBreaker})
  of ",":
    ret(30, {Left, Infix})
  of "*", "/", "%", "#":
    ret(60, {Left, Infix, Prefix, Postfix})
  of "and":
    ret(80, {Left, Infix})
  of "or":
    ret(70, {Left, Infix})
  of "in", "is", "notin", "isnt", "of":
    ret(120, {Left, Infix})
  of "==", "!=", "===", "~=":
    ret(120, {Left, Infix})
  of "<", ">":
    ret(130, {Left, Infix, Prefix})
  of "<=", ">=":
    ret(130, {Left, Infix})
  of "<<", ">>":
    ret(140, {Left, Infix, Prefix})
  of "+", "-":
    ret(150, {Left, Infix, Prefix, Postfix})
  of "++", "--", "?", "!", "&", "@":
    ret(180, {Right, Infix, Prefix, Postfix})
  of ":", "::":
    ret(190, {Left, Infix, Prefix})
  of ".":
    ret(200, {Left, Infix, Prefix, Postfix})
  else:
    result.precedence = -1

proc countIndent(line: string, c: char): int =
  for i in countup(0, line.len - 1):
    if line[i] != c: return i
  return -1

proc countIndents(lines: var TLines, indentMode: var TIndentMode): seq[int] =
  newSeq(result, lines.len)
  for i in countup(0, lines.len - 1):
    if lines[i].len == 0:
        result[i] = -1
        continue

    case indentMode
    of Unknown:
      if lines[i][0] == '\t':
        indentMode = Tabs
        result[i] = countIndent(lines[i], '\t')
      elif lines[i][0] == ' ':
        indentMode = Spaces
        result[i] = countIndent(lines[i], ' ')
      else: result[i] = 0
    of Tabs: result[i] = countIndent(lines[i], '\t')
    of Spaces: result[i] = countIndent(lines[i], ' ')

    if result[i] != 0:
      lines[i] = substr(lines[i], result[i])

    echo "LINE ", i, " ", result[i], ": ", lines[i]

proc debugCursor(g: PGripFile, cursor: TPos) =
  echo g.lines[cursor.line]
  echo(repeatChar(cursor.col, ' ') & "^")

proc readGripFile(filename: string, stream: PLLStream): PGripFile =
  new(result)
  result.fileIdx = fileInfoIdx(filename)
  result.indentMode = Unknown
  result.lines = llStreamReadAll(stream).splitLines
  result.indents = countIndents(result.lines, result.indentMode)

  gGripFiles.setLen(result.fileIdx + 1)
  gGripFiles[result.fileIdx] = result

proc charAt(g: PGripFile, line, col: int): char =
  if line >= g.lines.len or col >= g.lines[line].len: return EOF
  return g.lines[line][col]

proc charAt(g:PGripFile, p: TPos): char =
  return charAt(g, p.line, p.col)

proc eatChar(g: PGripFile, p: var TPos): char =
  let curLineLen = g.lines[p.line].len
  if p.col == curLineLen:
    p.col = int16(0)
    p.line += int16(1)
    if p.line >= g.lines.len: return EOF
  else:
    p.col += int16(1)

  return charAt(g, p)

iterator eatCharsInLine(g: PGripFile, pos: var TPos): char =
  # @@ yeild is broken right now and we can't yeild here
  # cheat a little bit so the yield inside the loop will
  # catch the first character
  if pos.col > int16(0): pos.col -= int16(1)

  while pos.col < g.lines[pos.line].len:
    inc pos.col
    yield charAt(g, pos)

proc pos(i: TLineInfo): TPos =
  result = newPos(i.line, i.col)

proc `<`(lhs, rhs: TPos): bool =
  if lhs.line < rhs.line: return true
  if lhs.line > rhs.line: return false
  return lhs.col < rhs.col

proc whitespaceFactor(c: TPrecedence): int =
  result = c.before.spaces + c.after.spaces

proc totalChars(ws: TWhiteSpace): int =
  result = ws.spaces + ws.tabs + ws.newlines

proc stepBack(g: PGripFile, p: TPos): TPos =
  result = p
  if p.col > 0:
    result.col -= int16(1)
  else:
    result.line -= int16(1)
    result.col = int16(g.lines[p.line].len - 1)

proc stepForward(g: PGripFile, p: TPos): TPos =
  result = p
  discard eatChar(g, result)

proc lineAt(g: PGripFile, p: TPos): string =
  return g.lines[p.line]

proc sourceText(g: PGripFile, begins, ends: TPos): string =
  assert begins < ends
  if begins >= ends: return ""

  if begins.line == ends.line:
    return substr(g.lines[begins.line], begins.col, ends.col)
  else:
    result = substr(g.lines[begins.line], begins.col)
    result.add "\n"

    for line in countup(begins.line + 1, ends.line - 1):
      result.add(g.lines[line])
      result.add "\n"

    result.add(substr(g.lines[ends.line], 0, ends.col))

proc lineinfo(g: PGripFile, p: TPos): TLineInfo =
  return newLineInfo(g.fileIdx, p.line, p.col)

proc lineinfo(g: PGripFile, line, col: int): TLineInfo =
  return newLineInfo(g.fileIdx, line, col)

template scanLine(g, p, charClass: expr, body: stmt): stmt {.immediate, dirty.} =
  var
    scanStart = p
    line = lineAt(g, p)
    e = line.len
    i = int(p.col)

  while i < e:
    let c = line[i]
    if c notin charClass: break
    body
    i += 1

  p.col = int16(i)

proc scanNum(g: PGripFile, p: var TPos): PNode =
  var n = 0
  scanLine(g, p, NumChars): n = n*10 + ord(c) - ord('0')

  result = newIntNode(nkIntLit, n)
  result.info = lineinfo(g, scanStart)

proc scanId(g: PGripFile, p: var TPos): PNode =
  scanLine(g, p, IDChars): discard
  let id = getIdent(line.substr(scanStart.col, i-1))
  result = newIdentNode(id, lineinfo(g, scanStart))

proc scanOp(g: PGripFile, p: var TPos): PNode =
  scanLine(g, p, OpChars): discard

  if i == scanStart.col: return scanId(g, p)

  let id = getIdent(line.substr(scanStart.col, i-1))
  result = newIdentNode(id, lineinfo(g, scanStart))

proc error(g: PGripFile, p: TPos, msg: TMsgKind, arg = "") =
  globalError(lineinfo(g, p), msg, arg)

proc tostring(c: char): string =
  result = newString(1)
  result[0] = c

proc scanToEnd(g: PGripFile, s,e: char, pos: var TPos): PNode =
  var count = 1

  var p = pos
  var start = stepForward(g, pos)

  while true:
    var c = eatChar(g, p)
    if c == EOF: error(g, p, errClosingXExpected, tostring(e))
    elif c == e:
      count -= 1
      if count == 0:
        result = newNodeI(nkTripleStrLit, lineinfo(g, start))
        result.ends = stepBack(g, p)
        pos = stepForward(g, p)
        return
    elif c == s:
      count += 1

proc scanWhiteSpace(g: PGripFile, pos: var TPos): TWhiteSpace =
  for c in eatCharsInLine(g, pos):
    if c notin {' ', '\t'}: break
    if c == ' ': result.spaces += 1
    else: result.tabs += 1

const nkLiterals = { nkIntLit, nkStrLit, nkFloatLit }

proc sexp(id: Pnode, sons: varargs[PNode]): PNode =
  if id.kind == nkIdent:
    if id.ident.id == ord(wDot):
      result = newNode(nkDotExpr, id.info, @[sons[0], sons[1]])
    else:
      result = newNodeI(nkCall, id.info)
      result.sons = @[id]
      result.sons.add(sons)
  else:
    internalAssert sons.len == 0
    return id

proc parseCall(g: PGripFile, s, e: int): PNode
proc parseExpr(g: PGripFile, pos: var TPos): PNode
proc parsePrimaryExpr(g: PGripFile, pos: var TPos): PNode

proc pushExp(s: var TShuntingYardStack, n: PNode) =
  s.expStackTop += 1
  s.expStack[s.expStackTop] = n

proc pushOp(s: var TShuntingYardStack, op: TPrecedence) =
  s.opStackTop += 1
  s.opStack[s.opStackTop] = op

proc clear(s: var TShuntingYardStack) =
  s.opStackTop = -1
  s.expStackTop = -1

proc popStacks(s: var TShuntingYardStack) =
  if Unary in s.opStack[s.opStackTop].opdat.flags:
    s.expStack[s.expStackTop] = sexp(
      s.opStack[s.opStackTop].id,
      s.expStack[s.expStackTop])

    s.opStackTop -= 1

  else:
    var i1, i2: int
    if Left in s.opStack[s.opStackTop].opdat.flags:
      i1 = 1
    else:
      i2 = 1

    s.expStack[s.expStackTop - 1] = sexp(
      s.opStack[s.opStackTop].id,
      s.expStack[s.expStackTop - i1],
      s.expStack[s.expStackTop - i2])

    s.expStackTop -= 1
    s.opStackTop -= 1

proc processOp(s: var TShuntingYardStack, op: TPrecedence) =
  # This implements the shunting yard algorithm explained here:
  # http://en.wikipedia.org/wiki/Shunting-yard_algorithm
  # Few modifications are made to support whitespace sensitivity and
  # prefix and postfix operators
  while s.opStackTop >= 0:
    let
      opWs = op.whitespaceFactor
      topWs = s.opStack[s.opStackTop].whitespaceFactor

    if opWs < topWs:
      break

    let
      nextPrecedence = op.opdat.precedence + ord(Left in op.opdat.flags)
      topPrecedence = s.opStack[s.opStackTop].opdat.precedence

    if opWs > topWs or nextPrecedence <= topPrecedence:
      popStacks(s)
    else:
      break

  pushOp(s, op)

proc debug(s: TShuntingYardStack) =
  for i in countup(0, s.opStackTop):
    echo "OP STACK ", i, " ", s.opStack[i].id.ident.s

  for i in countup(0, s.expStackTop):
    echo "EXP STACK ", i
    debug s.expStack[i]

proc parseIndexers(g: PGripFile, pos: var TPos, n: PNode): PNode =
  result = n
  let c = charAt(g, pos)
  case c
  of '(':
    let exp = scanToEnd(g, '(', ')', pos)
    result = newNode(nkCall, n.info, @[n, exp])
  of '[':
    let exp = scanToEnd(g, '[', ']', pos)
    # result.n = newNode(nkCall, e.n.info, @[getIdent"[]", result.n, exp.n])
    # kuresult.ends = exp.ends
  else:
    discard

proc firstCall(g: PGripFile, line: int): int =
  for i in line .. < g.lines.len:
    if g.indents[i] == -1: continue
    return i

  return g.lines.len

proc scanCall(g: PGripFile, start: int): int =
  let indent = g.indents[start]
  for i in countup(start + 1, g.indents.len - 1):
    if g.indents[i] != -1 and g.indents[i] <= indent:
      return i
  return g.indents.len

proc parseBlock(g: PGripFile, pos: var TPos): PNode =
  var
    line = firstCall(g, pos.line)
    indent = g.indents[line]
    totalLines = g.lines.len
    callEnd = 0

  result = newNode(nkStmtList)

  while true:
    callEnd = scanCall(g, line)
    let call = parseCall(g, line, callEnd)
    echo indent, " BLOCK ELEM ", line
    debug call
    result.addSon(call)
    if callEnd >= totalLines or g.indents[callEnd] < indent: break
    line = callEnd

  pos = newPos(int16(callEnd), int16(0))
  echo "BLOCK PARSED ", callEnd

proc parseNestedBlock(g: PGripFile, pos: var TPos): PNode =
  var
    parentIndent = g.indents[pos.line]
    nextLine = firstCall(g, pos.line + 1)

  pos = newPos(int16(nextLine), int16(0))

  if pos.line == g.lines.len or g.indents[pos.line] <= parentIndent:
    result = newNode(nkStmtList, lineinfo(g, pos), @[])
  else:
    result = parseBlock(g, pos)

proc parseBlockArgs(g: PGripFile, args, retType: PNode): PNode =
  echo "PARSING BLOCK ARGS"
  result = newNode(nkFormalParams, args.info, @[retType])
  var pos = args.info.pos
  while pos < args.ends:
    echo "PARSING NEXT ARG"
    result.addSon(parseExpr(g, pos))

proc isEmpty(ws: TWhiteSpace): bool =
  return ws.tabs == 0 and ws.spaces == 0 and ws.newlines == 0

proc isPrefix(op: TPrecedence): bool =
  if not op.after.isEmpty or op.before.isEmpty:
    return false

  if Prefix in op.opdat.flags:
    return true

  if Infix notin op.opdat.flags:
    globalError(op.id.info, errXCantBeUsedAsPrefix, op.id.ident.s)

  return false

proc isPostfix(op: TPrecedence): bool =
  if not op.before.isEmpty or op.after.isEmpty:
    return false

  if Postfix in op.opdat.flags:
    return true

  if Infix notin op.opdat.flags:
    globalError(op.id.info, errXCantBeUsedAsPostfix, op.id.ident.s)

  return false

proc parseWsAndOps(g: PGripFile, pos: var TPos, n: PNode): PNode =
  result = n

  var expChain: TShuntingYardStack
  clear(expChain)

  if n.kind == nkPrefix:
    # If the input expression already has a prefix operator,
    # feed it into the opstack so it can play nicely with
    # any following operators

    # the before/after will be auto set to 0 just like we need
    var op: TPrecedence
    op.id = n[0]
    op.opdat = getOp(n[0].ident)
    op.opdat.flags.incl Unary

    expChain.pushOp(op)
    expChain.pushExp(n[1])
  else:
    expChain.pushExp(result)

  while true:
    var next: TPrecedence
    next.before = scanWhiteSpace(g, pos)

    let c = charAt(g, pos)
    if c notin OpChars + IDStartChars:
      echo "breaking after ws"
      break

    var preOp = pos
    next.id = scanOp(g, pos)
    next.opdat = getOp(next.id.ident)
    if next.opdat.precedence == -1:
      if c in OpChars:
        error(g, pos, errInvalidOperator, next.id.ident.s)
      else:
        pos = preOp
        break

    next.after = scanWhiteSpace(g, pos)

    if CallBreaker in next.opdat.flags:
      g.pendingOp = next
      g.breakCall = true
      break

    if isPrefix(next):
      pos.col = next.id.info.col
      break

    expChain.processOp(next)

    if isPostfix(next):
      expChain.opStack[expChain.opStackTop].opdat.flags.incl Unary
      # backtrack a little bit so the next op can compute
      # its leading whitespace correctly
      pos.col -= next.after.totalChars.int16
      continue

    expChain.pushExp(parsePrimaryExpr(g, pos))

  while expChain.opStackTop >= 0:
    expChain.popStacks()

  result = expChain.expStack[0]

proc hasNestedBlock(g: PGripFile, pos: TPos): bool =
  return
    g.indents.len > pos.line and
    g.indents[pos.line] < g.indents[pos.line + 1]

proc parsePrimaryExpr(g: PGripFile, pos: var TPos): PNode =
  var start = pos
  let c = charAt(g, pos)
  echo "PRIMARY EXPR ", c
  case c
  of IDStartChars:
    result = scanId(g, pos)

  of OpChars:
    let op = scanOp(g, pos)
    let exp = parsePrimaryExpr(g, pos)
    result = newNode(nkPrefix, op.info, @[op, exp])

  of NumStartChars:
    result = scanNum(g, pos)

  of '(':
    var parens = scanToEnd(g, '(', ')', pos)
    result = newNode(nkPar, lineinfo(g, start), @[parens])

  of '[':
    var
      args = scanToEnd(g, '[', ']', pos)
      ws = scanWhiteSpace(g, pos)
      retType = emptyNode
      c = charAt(g, pos)
      body: PNode

    args = parseBlockArgs(g, args, retType)

    if c == ':':
      discard eatChar(g, pos)
      ws = scanWhiteSpace(g, pos)
      retType = parseExpr(g, pos)
      echo "after type"
      debugCursor g, pos
    if charAt(g, pos) != EOF:
      echo "trying to parse body"
      # @@ turn this into parseCall
      body = parseExpr(g, pos)
    else:
      echo "trying nested block"
      body = parseNestedBlock(g, pos)

    result = newNode(nkLambda, lineinfo(g, start), @[emptyNode, emptyNode, args, emptyNode, body])

  of '{':
    var parens = scanToEnd(g, '{', '}', pos)
    result = newNode(nkPar, lineinfo(g, start), @[parens])

  of StrStartChars:
    let range = scanToEnd(g, c, c, pos)
    result = newStrNode(nkStrLit, sourceText(g, range.info.pos, range.ends))
    result.info = range.info

  else:
    echo "in PARSE EXPR"
    debugCursor g, pos
    error(g, pos, errUnexpectedCharacter, tostring(c))

  if pos.line == result.info.line:
    result = parseIndexers(g, pos, result)

  echo "END PRIMARY"

proc parseExpr(g: PGripFile, pos: var TPos): PNode =
  echo "PARSE EXPR"

  result = parsePrimaryExpr(g, pos)
  result = parseWsAndOps(g, pos, result)

  echo "END PARSE EXPR"
  debugCursor g, pos

proc isLineEnd(g: PGripFile, p: TPos): bool =
  return p.col >= g.lines[p.line].len

proc parseCall(g: PGripFile, s, e: int): PNode =
  var pos = newPos(int16(s), int16(0))
  var callChain: TShuntingYardStack
  clear(callChain)

  block ParseLine:
    while true:
      g.breakCall = false
      let callee = parseExpr(g, pos)
      echo "parsing call "
      debug callee
      echo "after debyg"
      var call = sexp(callee)
      echo "After sexp"
      callChain.pushExp(call)
      echo "after call chain"

      if false and isLineEnd(g, pos):
        # @@ Why was this needed?
        if hasNestedBlock(g, pos):
          var start = pos
          var body = parseNestedBlock(g, pos)
          var args = newNode(nkFormalParams, lineinfo(g, start), @[emptyNode])
          call.addSon newNode(nkLambda, lineinfo(g, start), @[emptyNode, emptyNode, args, emptyNode, body])
        else:
          break ParseLine

      while true:
        echo "PARSE CALL STEP"
        if g.breakCall:
          echo "CALL BROKEN by ", g.pendingOp.id.ident.s
          callChain.processOp(g.pendingOp)
          debug callChain
          break

        if isLineEnd(g, pos):
          echo "LINE AT END"
          if hasNestedBlock(g, pos):
            echo "NESTED BLOCK"
            var start = pos
            var body = parseNestedBlock(g, pos)
            var args = newNode(nkFormalParams, lineinfo(g, start), @[emptyNode])
            call.addSon newNode(nkLambda, lineinfo(g, start), @[emptyNode, emptyNode, args, emptyNode, body])
            break ParseLine
          else:
            break ParseLine
        else:
          let param = parseExpr(g, pos)
          call.addSon(param)

  while callChain.opStackTop >= 0:
    popStacks(callChain)

  return callChain.expStack[0]

proc parse(filename: string, stream: PLLStream): PNode =
  var
    g = readGripFile(filename, stream)
    pos = newPos(int16(0), int16(0))

  result = parseBlock(g, pos)
  echo "PARSE COMPLETE"
  debug result

proc carryPass(p: TPass, module: PSym, m: TPassData): TPassData =
  var c = p.open(module)
  result.input = p.process(c, m.input)
  result.closeOutput = p.close(c, m.closeOutput)

proc CompileGrip(module: PSym, filename: string, stream: PLLStream) =
  var nodes = parse(filename, stream)

  var nimSem = semPass
  var c = nimSem.open(module).PContext
  c.inGripContext = true

  for i in 0.. <nodes.sonsLen:
    nodes.sons[i] = semGrip(c, nodes[i])

  var passData = (input: nodes, closeOutput: nimSem.close(c, nil))
  discard carryPass(cgenPass, module, passData)

passes.grip = CompileGrip

