package bshapeless.exprs

import scala.annotation.unchecked.uncheckedVariance

trait ExprBuilder[-T <: ExprTree {type ATT <: T@uncheckedVariance} ,R] {

  def build(x: T): R = x.build(this)

  def buildHNil: R
  def buildHList(h: T, t: T): R
  def buildCNil: R
  def buildCoproduct(h: T, t: T): R
  def buildSelectArg(n: Int): R
  def buildFromArg: R
  def buildSelectCtx(n: Int): R
  def buildApply(f: T, a: T): R
  def buildApplyNative(name: String, memberFunc: Boolean, arg: T): R
  def buildPair(f: T, s: T): R
  def buildAbstractVal(b: T): R
  def buildAbstractFun(b: T): R
  def buildInlResult(a: T): R
  def buildInrResult(a: T): R
}

trait ExprBuilderAbstract[R] extends ExprBuilder[ExprTree, R]