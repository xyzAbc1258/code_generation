package bshapeless.exprs

import scala.annotation.unchecked.uncheckedVariance
import scala.reflect.internal.annotations.uncheckedBounds

trait ExprBuilderGeneric[-T <: ExprTree {type ATT <: T@uncheckedVariance} ,R, W[_]] {

  def build(x: T): R = x.build[R](this.asInstanceOf[ExprBuilderGeneric[x.ATT, R, x.W]@uncheckedBounds])

  def buildHNil: R
  def buildHList(h: T, t: T): R
  def buildCNil: R
  def buildCoproduct(h: T, t: T): R
  def buildSelectArg(n: Int): R
  def buildFromArg: R
  def buildSelectCtx(n: Int): R
  def buildApply(f: T, a: T): R
  def buildApplyNative(name: String, func: W[(_) => _], memberFunc: Boolean, arg: T): R
  def buildPair(f: T, s: T): R
  def buildAbstractVal(b: T): R
  def buildAbstractFun(b: T): R
  def buildInlResult(a: T): R
  def buildInrResult(a: T): R
}

object ExprBuilderGeneric {
  type ExprBuilder[-T <: ExprTree {type ATT <: T@uncheckedVariance} ,R] = ExprBuilderGeneric[T, R, ({type I[A] = A})#I]
  type ExprBuilderAbstract[R] = ExprBuilder[ExprTree, R]
}