package generation.exprs

sealed trait ExprType

object ExprType {

  case object HNilTree extends ExprType

  case object HListResult extends ExprType

  case object CNilArg extends ExprType

  case object CoproductArgs extends ExprType

  case object SelectArgs extends ExprType

  case object FromArgsEq extends ExprType

  case object SelectCtx extends ExprType

  case object Apply extends ExprType

  case object ApplyNative extends ExprType

  case object Pair extends ExprType

  case class AbstractVal(argIsHList: Boolean) extends ExprType

  case object AbstractFun extends ExprType

  case object InlResult extends ExprType

  case object InrResult extends ExprType

}

