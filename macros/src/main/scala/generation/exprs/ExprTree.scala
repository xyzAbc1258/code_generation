package generation.exprs

trait ExprTree {
  x =>

  type ATT >: this.type <: (ExprTree {type ATT = x.ATT})
  type W[A]

  type Builder[R] = ExprBuilderGeneric[ATT, R, W]

  def typ: ExprType
  def build[R](b: ExprBuilderGeneric[ATT, R, W]): R
}
