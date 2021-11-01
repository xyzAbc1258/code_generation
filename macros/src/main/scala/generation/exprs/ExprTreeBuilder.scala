package generation.exprs

import generation.exprs

class ExprTreeBuilder[W[_]](eval: W[_] => Any) extends ExprBuilderGeneric[ExprTree, Expr[Nothing, Nothing, Nothing], W] {

  implicit def asNothing(e: Expr[_, _, _]): Expr[Nothing, Nothing, Nothing] = e.asInstanceOf

  override def buildHNil: Expr[Nothing, Nothing, Nothing] =
    exprs.HNilCreate[Nothing, Nothing]

  override def buildHList(h: ExprTree, t: ExprTree): Expr[Nothing, Nothing, Nothing] = {
    exprs.HListResultSplit[Nothing, Nothing, Nothing, Nothing](build(h), build(t))
  }

  override def buildCNil: Expr[Nothing, Nothing, Nothing] =
    exprs.CNilCreate[Nothing, Nothing]

  override def buildCoproduct(h: ExprTree, t: ExprTree): Expr[Nothing, Nothing, Nothing] =
    exprs.CoproductArgSplit[Nothing, Nothing, Nothing, Nothing](build(h), build(t))

  override def buildSelectArg(n: Int): Expr[Nothing, Nothing, Nothing] =
    exprs.FromArgsSelect(n)

  override def buildFromArg: Expr[Nothing, Nothing, Nothing] =
    exprs.FromArgsEq[Nothing, Nothing, Nothing](implicitly[Nothing <:< Nothing])

  override def buildSelectCtx(n: Int): Expr[Nothing, Nothing, Nothing] =
    exprs.FromCtxSelect(n)

  override def buildApply(f: ExprTree, a: ExprTree): Expr[Nothing, Nothing, Nothing] =
    exprs.Apply[Nothing, Nothing, Nothing, Nothing](build(f), build(a))

  override def buildApplyNative(name: String, func: W[(_) => _], memberFunc: Boolean, arg: ExprTree): Expr[Nothing, Nothing, Nothing] = {
    val f: Nothing => Nothing = eval(func).asInstanceOf[Nothing => Nothing]
    exprs.ApplyNative[Nothing, Nothing, Nothing, Nothing](build(arg))(f, name, memberFunc)
  }

  override def buildPair(f: ExprTree, s: ExprTree): Expr[Nothing, Nothing, Nothing] = {
    exprs.PairExp[Nothing, Nothing, Nothing, Nothing](build(f), build(s))
  }

  override def buildAbstractVal(b: ExprTree, isArgHList: Boolean, argType: W[String]): Expr[Nothing, Nothing, Nothing] = {
    if (isArgHList)
      exprs.AbstractVal[Nothing, Nothing, Nothing, Nothing](build(b).asInstanceOf)
    else
      exprs.AbstractValNotH[Nothing, Nothing, Nothing, Nothing](build(b).asInstanceOf)
  }

  override def buildAbstractFun(b: ExprTree, argType: W[String]): Expr[Nothing, Nothing, Nothing] =
    exprs.AbstractFunc[Nothing, Nothing, Nothing, Nothing](build(b).asInstanceOf)

  override def buildInlResult(a: ExprTree): Expr[Nothing, Nothing, Nothing] =
    exprs.InlResultExpr[Nothing, Nothing, Nothing, Nothing](build(a))

  override def buildInrResult(a: ExprTree): Expr[Nothing, Nothing, Nothing] =
    exprs.InrResultExpr[Nothing, Nothing, Nothing, Nothing](build(a))
}
