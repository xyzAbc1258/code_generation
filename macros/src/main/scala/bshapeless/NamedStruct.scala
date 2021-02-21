package bshapeless

import shapeless._

trait NamedStruct[L, T] {
  type NamedType

  def deriveHList[H, HT <: HList](h: NamedType)(implicit ev: L <:< (H :: HT)):(
    ((X, NamedStruct.Aux[H, T, X]), (Y, NamedStruct.Aux[HT, T, Y])) forSome {type X; type Y}
    ) = {
    val cons = h.asInstanceOf[shapeless.::[_, _ <: HList]]
    ((cons.head, NamedStruct.instance[H, T, Any]),
      (cons.tail, NamedStruct.instance[HT, T, HList]))
  }

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
