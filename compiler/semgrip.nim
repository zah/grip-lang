# included from sem.nim

proc preSemGrip*(c: PContext, n: PNode): PNode

proc gripStmtList(c: PContext, n: PNode): PNode =
  if n.kind == nkLambda:
    echo "LAMBDA ", n.sonsLen
    result = n[4]
  else:
    result = n

  for i in 0 .. <result.len:
    result.sons[i] = preSemGrip(c, result[i])

proc gripIf(c: PContext, n: PNode): PNode =
  result = newNode(nkIfStmt, n.info, @[
    newNode(nkElifBranch, n.info, @[n[1], gripStmtList(c, n[2])])
  ])

proc buildIfFromElse(c: PContext, n: PNode): PNode =
  let previous = n[1]
  case previous.ident.id
  of ord(wIf):
    result = gripIf(c, previous)
  of ord(wElse):
    result = buildIfFromElse(c, previous)
  else:
    internalAssert false

  result.addSon(newNode(nkElse, n.info, @[gripStmtList(c, n[2])]))

proc tryConst(c: PContext, n: PNode): PNode =
  result  = semExprWithType(c, n)
  if result != nil:
    result = evalConstExpr(c.module, result)

const skVars = {skVar, skLet, skForVar, skParam}

proc newVarSection(lhs, rhs: PNode, isConst: bool): PNode =
  var sectionKind, defKind: TNodeKind
  if isConst:
    sectionKind = nkConstSection
    defKind = nkConstDef
  else:
    sectionKind = nkVarSection
    defKind = nkIdentDefs

  result = newNode(sectionKind, lhs.info, @[
    newNode(defKind, lhs.info, @[lhs, emptyNode, rhs])
  ])

proc expectIdent(n: PNode, idx: int): PIdent =
  internalAssert idx < n.len
  internalAssert n[idx].kind == nkIdent
  return n[idx].ident

proc expectKind(n: PNode, idx: int, kind: TNodeKind): PNode =
  internalAssert idx < n.len and n[idx].kind == kind
  return n[idx]

proc gripTypeSection(c: PContext; name, body: PNode):
  tuple[typedef: PNode, constructors: PNode] =
  
  var recList = newNode(nkRecList, name.info, @[])
  var genericParams = emptyNode
  var pragmas = emptyNode
  var baseType = emptyNode

  result.typedef =
    newNode(nkTypeDef, name.info, @[
      name,
      genericParams,
      newNode(nkObjectTy, body.info, @[
        pragmas,
        baseType,
        recList])])

  try:
    c.gripTypeSection = GripTypeSectionContext(
      prev: c.gripTypeSection,
      typ: result.typedef)

    discard openScope(c)
    echo "BODY "
    debug body[bodyPos]
    body.sons[bodyPos] = preSemGrip(c, body[bodyPos])
    var constructor = semProcAux(c, body, skProc, procPragmas)
  
  finally:
    closeScope(c)
    c.gripTypeSection = c.gripTypeSection.prev
    
proc inMainConstructor(c: PContext): bool =
  return c.gripTypeSection != nil # TODO: check we are also not in a nested method

proc isTypeField(n: PNode): bool =
  return n.kind == nkDotExpr and n.len == 1

proc fieldName(n: PNode): PNode =
  return n[1]

proc preSemGrip(c: PContext, n: PNode): PNode =
  result = n
 
  if n.kind == nkStmtList:
    result = gripStmtList(c, n)
  elif n.kind == nkCall:
    case n.sons[0].ident.id
    of ord(wFn):
      var def = n.sons[2]
      def.sons[0] = n.sons[1]
      var params = def[3]
      for i in 1.. <params.sons.len:
        let exp = params[i]
        if exp.kind == nkIdent:
          params.sons[i] = newNode(nkIdentDefs, exp.info, @[exp, emptyNode, emptyNode])
        elif exp.kind == nkCall:
          params.sons[i] = newNode(nkIdentDefs, exp.info, @[exp[1], exp[2], emptyNode])
  
      def.kind = nkProcDef
      result = def
    
    of ord(wEquals):
      checkSonsLen n, 3
      var
        lhs = c.preSemGrip n[1]
        rhs = c.preSemGrip n[2]
      
      if c.inMainConstructor and lhs.isTypeField:
        let typedRhs = semExprWithType(c, rhs)
        let fieldName = lhs.fieldName
        lhs = newNode(nkDotExpr, lhs.info, @[newIdentNode(getIdent"result", lhs.info), fieldName])
    
      result = newNode(nkAsgn, n.info, @[lhs, rhs])
 
    of ord(wGripComment):
      result = emptyNode
    
    of ord(wType):
      let typeName = n.expectKind(1, nkIdent)
      let body = n.expectKind(2, nkLambda)
      
      var typeSection = newNode(nkTypeSection, n.info)
      
      var typ = gripTypeSection(c, typeName, body)
      typeSection.add typ.typedef
      
      result = semTypeSection(c, typeSection)

    of ord(wIf):
      result = gripIf(c, n)
    
    of ord(wElse):
      result = buildIfFromElse(c, n)
    
    of ord(wFor):
      let
        set = n[1]
        iter = n[2]
        id = iter[paramsPos][1]
      result = newNode(nkForStmt, n.info, @[id, set, iter[bodyPos]])
    
    of ord(wWhile):
      let condition = n[1]
      let body = n[2][bodyPos]
      result = newNode(nkWhileStmt, n.info, @[condition, body])
    
    else:
      discard
  

proc semGrip*(c: PContext, n: PNode): PNode =
  result = preSemGrip(c, n)
  result = myProcess(c, result)

