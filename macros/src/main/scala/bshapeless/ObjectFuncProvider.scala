package bshapeless

import shapeless._
import shapeless.Nat
import shapeless.ops.hlist.Repeat
import shapeless.ops.nat.ToInt

sealed trait ObjectFuncProvider[+T]

object ObjectFuncProvider extends ObjectFuncProvider[Nothing] {

  @inline def list[N <: Nat](implicit h: Repeat[this.type :: HNil, N], toInt: ToInt[N]): h.Out =
    (1 to toInt()).foldLeft[HList](HNil){case (h, _) => this :: h}.asInstanceOf[h.Out]

}