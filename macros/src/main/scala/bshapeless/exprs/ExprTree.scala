package bshapeless.exprs

trait ExprTree {
  x =>

  type ATT >: this.type <: (ExprTree {type ATT = x.ATT})

  def typ: ExprType
  def build[R](b: ExprBuilder[ATT, R]): R
}
