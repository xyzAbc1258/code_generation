package bshapeless.utils

import scala.reflect.api.Universe

class CommonTypeOps[U <: Universe with Singleton](val pair: (U,U#Type, Types[U])) extends AnyVal {

  @inline private def a2: U#Type = pair._2
  @inline private def universe: U = pair._1
  @inline private def Types: Types[U] = pair._3

  private def apply(tycon: U#Type, args: U#Type*): U#Type =
    universe.appliedType(tycon, args.toList:_*)

  private def isSubType(t: U#Type, expected: U#Type): Boolean =
    t <:< expected

  def ::::(a1: U#Type): U#Type = { //Methods ending with colon bind to right eg. t1 :::: t2 == t2.::::(t1)
    assert(isSubType(a2, Types.hlistType), a2)
    apply(Types.hconsType.typeConstructor, a1, a2)
  }

  def +:+:(a1: U#Type): U#Type = {
    assert(isSubType(a2, Types.coproductType))
    universe.appliedType(Types.cconsType.typeConstructor, a1, a2)
  }

  def ==>(a1: U#Type): U#Type = universe.appliedType(Types.funcType.typeConstructor, a2, a1)

  def collect: Set[U#Type] = {
    val c = scala.collection.mutable.ListBuffer.empty[U#Type]
    a2.foreach(c.append)
    c.toSet
  }

  def firstTypeArg: U#Type = a2.typeArgs.head
  def secondTypeArg: U#Type = a2.typeArgs.tail.head
}