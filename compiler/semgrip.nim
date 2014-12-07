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

proc preSemGrip(c: PContext, n: PNode): PNode =
  result = n
  
  echo "ENTERING SEM GRIP"
  debug n
  
  if n.kind == nkCall:
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
      if n[1].kind == nkCall and n[1].sonsLen == 1 and n[1][0].kind == nkIdent:
        let
          lhs = n[1][0]
          rhs = n[2]
          rhsAsConst = PNode nil # tryConst(c, rhs)

        if rhsAsConst != nil:
          result = newVarSection(lhs, rhsAsConst, true)
        else:
          var existingVar = localSearchInScope(c, lhs.ident)
          if existingVar != nil:
            let varSym = semSym(c, lhs, existingVar, {})
            result = newNode(nkAsgn, n.info, @[varSym, rhs])
          else:
            result = newVarSection(lhs, rhs, false)

      else:
        echo "BAD ASSIGNMENT"

      echo "DECLARING VAR"
      debug result

    of ord(wGripComment):
      result = emptyNode
    of ord(wType):
      echo "type"
      result = emptyNode
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
  
  echo "EXITING SEM GRIP"
  debug result

proc semGrip*(c: PContext, n: PNode): PNode =
  result = preSemGrip(c, n)
  result = myProcess(c, result)

