#
#
#           The Nim Compiler
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# This include file implements the semantic checking for magics.
# included from sem.nim

proc semAddr(c: PContext; n: PNode; isUnsafeAddr=false): PNode =
  result = newNodeI(nkAddr, n.info)
  let x = semExprWithType(c, n)
  if x.kind == nkSym:
    x.sym.flags.incl(sfAddrTaken)
  if isAssignable(c, x, isUnsafeAddr) notin {arLValue, arLocalLValue}:
    localError(n.info, errExprHasNoAddress)
  result.add x
  result.typ = makePtrType(c, x.typ)

proc semTypeOf(c: PContext; n: PNode): PNode =
  result = newNodeI(nkTypeOfExpr, n.info)
  let typExpr = semExprWithType(c, n, {efInTypeof})
  result.add typExpr
  result.typ = makeTypeDesc(c, typExpr.typ)

type
  SemAsgnMode = enum asgnNormal, noOverloadedSubscript, noOverloadedAsgn

proc semAsgn(c: PContext, n: PNode; mode=asgnNormal): PNode
proc semSubscript(c: PContext, n: PNode, flags: TExprFlags): PNode

proc skipAddr(n: PNode): PNode {.inline.} =
  (if n.kind == nkHiddenAddr: n.sons[0] else: n)

proc semArrGet(c: PContext; n: PNode; flags: TExprFlags): PNode =
  result = newNodeI(nkBracketExpr, n.info)
  for i in 1..<n.len: result.add(n[i])
  result = semSubscript(c, result, flags)
  if result.isNil:
    let x = copyTree(n)
    x.sons[0] = newIdentNode(getIdent"[]", n.info)
    bracketNotFoundError(c, x)
    #localError(n.info, "could not resolve: " & $n)
    result = n

proc semArrPut(c: PContext; n: PNode; flags: TExprFlags): PNode =
  # rewrite `[]=`(a, i, x)  back to ``a[i] = x``.
  let b = newNodeI(nkBracketExpr, n.info)
  b.add(n[1].skipAddr)
  for i in 2..n.len-2: b.add(n[i])
  result = newNodeI(nkAsgn, n.info, 2)
  result.sons[0] = b
  result.sons[1] = n.lastSon
  result = semAsgn(c, result, noOverloadedSubscript)

proc semAsgnOpr(c: PContext; n: PNode): PNode =
  result = newNodeI(nkAsgn, n.info, 2)
  result.sons[0] = n[1]
  result.sons[1] = n[2]
  result = semAsgn(c, result, noOverloadedAsgn)

proc semIsPartOf(c: PContext, n: PNode, flags: TExprFlags): PNode =
  var r = isPartOf(n[1], n[2])
  result = newIntNodeT(ord(r), n)

proc expectIntLit(c: PContext, n: PNode): int =
  let x = c.semConstExpr(c, n)
  case x.kind
  of nkIntLit..nkInt64Lit: result = int(x.intVal)
  else: localError(n.info, errIntLiteralExpected)

proc semInstantiationInfo(c: PContext, n: PNode): PNode =
  result = newNodeIT(nkPar, n.info, n.typ)
  let idx = expectIntLit(c, n.sons[1])
  let useFullPaths = expectIntLit(c, n.sons[2])
  let info = getInfoContext(idx)
  var filename = newNodeIT(nkStrLit, n.info, getSysType(tyString))
  filename.strVal = if useFullPaths != 0: info.toFullPath else: info.toFilename
  var line = newNodeIT(nkIntLit, n.info, getSysType(tyInt))
  line.intVal = toLinenumber(info)
  result.add(filename)
  result.add(line)

proc toNode(t: PType, i: TLineInfo): PNode =
  result = newNodeIT(nkType, i, t)

const
  # these are types that use the bracket syntax for instantiation
  # they can be subjected to the type traits `genericHead` and
  # `Uninstantiated`
  tyUserDefinedGenerics* = {tyGenericInst, tyGenericInvocation,
                            tyUserTypeClassInst}

  tyMagicGenerics* = {tySet, tySequence, tyArray, tyOpenArray}

  tyGenericLike* = tyUserDefinedGenerics +
                   tyMagicGenerics +
                   {tyCompositeTypeClass}

proc uninstantiate(t: PType): PType =
  result = case t.kind
    of tyMagicGenerics: t
    of tyUserDefinedGenerics: t.base
    of tyCompositeTypeClass: uninstantiate t.sons[1]
    else: t

proc buildVTableType(c: PContext, con: PType): PType =
  # try getting the value from cache
  var
    wildcardType = errorType(c)
    diagnostics: seq[string] = @[]
    boundTypes: TIdTable
  initIdTable(boundTypes)
  
  let match = matchConcept(c, con, wildcardType, boundTypes, diagnostics)
  if match == nil:
    for d in diagnostics:
      echo d
      return errorType(c)

proc evalTypeTrait(c: PContext, traitCall: PNode, operand: PType): PNode =
  var owner = getCurrOwner(c)
  const skippedTypes = {tyTypeDesc, tyAlias}
  let trait = traitCall[0]
  internalAssert trait.kind == nkSym
  var operand = operand.skipTypes(skippedTypes)

  template operand2: PType =
    traitCall.sons[2].typ.skipTypes({tyTypeDesc})

  template typeWithSonsResult(kind, sons): PNode =
    newTypeWithSons(owner, kind, sons).toNode(traitCall.info)

  case trait.sym.name.s
  of "or", "|":
    return typeWithSonsResult(tyOr, @[operand, operand2])
  of "and":
    return typeWithSonsResult(tyAnd, @[operand, operand2])
  of "not":
    return typeWithSonsResult(tyNot, @[operand])
  of "name":
    result = newStrNode(nkStrLit, operand.typeToString(preferTypeName))
    result.typ = newType(tyString, owner)
    result.info = traitCall.info
  of "vtptr", "vtref":
    debug operand
    if operand.kind notin tyUserTypeClasses:
      localError(traitCall.info,
                 trait.sym.name.s & " must be used with a concept type")
      return emptyNode
    let vtableType = buildVTableType(c, operand)
    result = vtableType.toNode(traitCall.info)
  of "arity":
    result = newIntNode(nkIntLit, operand.len - ord(operand.kind==tyProc))
    result.typ = newType(tyInt, owner)
    result.info = traitCall.info
  of "genericHead":
    var res = uninstantiate(operand)
    if res == operand and res.kind notin tyMagicGenerics:
      localError(traitCall.info,
        "genericHead expects a generic type. The given type was " &
        typeToString(operand))
      return newType(tyError, owner).toNode(traitCall.info)
    result = res.base.toNode(traitCall.info)
  of "stripGenericParams":
    result = uninstantiate(operand).toNode(traitCall.info)
  of "supportsCopyMem":
    let t = operand.skipTypes({tyVar, tyGenericInst, tyAlias, tyInferred})
    let complexObj = containsGarbageCollectedRef(t) or
                     hasDestructor(t)
    result = newIntNodeT(ord(not complexObj), traitCall)
  else:
    localError(traitCall.info, "unknown trait")
    result = emptyNode

proc semTypeTraits(c: PContext, n: PNode): PNode =
  checkMinSonsLen(n, 2)
  let t = n.sons[1].typ
  internalAssert t != nil and t.kind == tyTypeDesc
  if t.sonsLen > 0:
    # This is either a type known to sem or a typedesc
    # param to a regular proc (again, known at instantiation)
    result = evalTypeTrait(c, n, t)
  else:
    # a typedesc variable, pass unmodified to evals
    result = n

proc semOrd(c: PContext, n: PNode): PNode =
  result = n
  let parType = n.sons[1].typ
  if isOrdinalType(parType):
    discard
  elif parType.kind == tySet:
    result.typ = makeRangeType(c, firstOrd(parType), lastOrd(parType), n.info)
  else:
    localError(n.info, errOrdinalTypeExpected)
    result.typ = errorType(c)

proc semBindSym(c: PContext, n: PNode): PNode =
  result = copyNode(n)
  result.add(n.sons[0])

  let sl = semConstExpr(c, n.sons[1])
  if sl.kind notin {nkStrLit, nkRStrLit, nkTripleStrLit}:
    localError(n.sons[1].info, errStringLiteralExpected)
    return errorNode(c, n)

  let isMixin = semConstExpr(c, n.sons[2])
  if isMixin.kind != nkIntLit or isMixin.intVal < 0 or
      isMixin.intVal > high(TSymChoiceRule).int:
    localError(n.sons[2].info, errConstExprExpected)
    return errorNode(c, n)

  let id = newIdentNode(getIdent(sl.strVal), n.info)
  let s = qualifiedLookUp(c, id, {checkUndeclared})
  if s != nil:
    # we need to mark all symbols:
    var sc = symChoice(c, id, s, TSymChoiceRule(isMixin.intVal))
    result.add(sc)
  else:
    errorUndeclaredIdentifier(c, n.sons[1].info, sl.strVal)

proc semShallowCopy(c: PContext, n: PNode, flags: TExprFlags): PNode

proc isStrangeArray(t: PType): bool =
  let t = t.skipTypes(abstractInst)
  result = t.kind == tyArray and t.firstOrd != 0

proc semOf(c: PContext, n: PNode): PNode =
  if sonsLen(n) == 3:
    n.sons[1] = semExprWithType(c, n.sons[1])
    n.sons[2] = semExprWithType(c, n.sons[2], {efDetermineType})
    #restoreOldStyleType(n.sons[1])
    #restoreOldStyleType(n.sons[2])
    let a = skipTypes(n.sons[1].typ, abstractPtrs)
    let b = skipTypes(n.sons[2].typ, abstractPtrs)
    let x = skipTypes(n.sons[1].typ, abstractPtrs-{tyTypeDesc})
    let y = skipTypes(n.sons[2].typ, abstractPtrs-{tyTypeDesc})

    if x.kind == tyTypeDesc or y.kind != tyTypeDesc:
      localError(n.info, errXExpectsObjectTypes, "of")
    elif b.kind != tyObject or a.kind != tyObject:
      localError(n.info, errXExpectsObjectTypes, "of")
    else:
      let diff = inheritanceDiff(a, b)
      # | returns: 0 iff `a` == `b`
      # | returns: -x iff `a` is the x'th direct superclass of `b`
      # | returns: +x iff `a` is the x'th direct subclass of `b`
      # | returns: `maxint` iff `a` and `b` are not compatible at all
      if diff <= 0:
        # optimize to true:
        message(n.info, hintConditionAlwaysTrue, renderTree(n))
        result = newIntNode(nkIntLit, 1)
        result.info = n.info
        result.typ = getSysType(tyBool)
        return result
      elif diff == high(int):
        localError(n.info, errXcanNeverBeOfThisSubtype, typeToString(a))
  else:
    localError(n.info, errXExpectsTwoArguments, "of")
  n.typ = getSysType(tyBool)
  result = n

proc magicsAfterOverloadResolution(c: PContext, n: PNode,
                                   flags: TExprFlags): PNode =
  case n[0].sym.magic
  of mAddr:
    checkSonsLen(n, 2)
    result = semAddr(c, n.sons[1], n[0].sym.name.s == "unsafeAddr")
  of mTypeOf:
    checkSonsLen(n, 2)
    result = semTypeOf(c, n.sons[1])
  of mArrGet: result = semArrGet(c, n, flags)
  of mArrPut: result = semArrPut(c, n, flags)
  of mAsgn:
    if n[0].sym.name.s == "=":
      result = semAsgnOpr(c, n)
    else:
      result = n
  of mIsPartOf: result = semIsPartOf(c, n, flags)
  of mTypeTrait: result = semTypeTraits(c, n)
  of mAstToStr:
    result = newStrNodeT(renderTree(n[1], {renderNoComments}), n)
    result.typ = getSysType(tyString)
  of mInstantiationInfo: result = semInstantiationInfo(c, n)
  of mOrd: result = semOrd(c, n)
  of mOf: result = semOf(c, n)
  of mHigh, mLow: result = semLowHigh(c, n, n[0].sym.magic)
  of mShallowCopy: result = semShallowCopy(c, n, flags)
  of mNBindSym: result = semBindSym(c, n)
  of mProcCall:
    result = n
    result.typ = n[1].typ
  of mDotDot:
    result = n
  of mRoof:
    localError(n.info, "builtin roof operator is not supported anymore")
  of mPlugin:
    let plugin = getPlugin(n[0].sym)
    if plugin.isNil:
      localError(n.info, "cannot find plugin " & n[0].sym.name.s)
      result = n
    else:
      result = plugin(c, n)
  else: result = n
