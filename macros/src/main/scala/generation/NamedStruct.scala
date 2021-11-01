package generation

import shapeless._

/**
 * Proof that NamedType has the same structure as type L but with types T.
 * E.g. if L is Hlist, NamedType is also HList of same length, but with elements of type T
 * @tparam L
 * @tparam T
 */
trait NamedStruct[L, T] {
  type NamedType
}

object NamedStruct {

  type Aux[L, T, H] = NamedStruct[L, T] {type NamedType = H}

  def instance[L, T, H]: Aux[L, T, H] = new NamedStruct[L, T] {
    override type NamedType = H
  }

  implicit def homoNotHListNotCoproduct[H, T](
    implicit e1: H <:!< HList
  ): Aux[H, T, T] = instance

  implicit def homoHNil[T]: Aux[HNil, T, HNil] = instance[HNil, T, HNil]

  implicit def homoCons[L <: HList, H, T](
    implicit homoEv: NamedStruct[L, T] {type NamedType <: HList},
    homoH: NamedStruct[H, T]
  ): Aux[H :: L, T, homoH.NamedType :: homoEv.NamedType] = instance

}
