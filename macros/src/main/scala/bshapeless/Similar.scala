package bshapeless

import shapeless._

trait Similar[H1, H2]

object Similar {

  private val obj = new Similar[Nothing, Nothing] {}

  def create[H1, H2]: Similar[H1, H2] =
    obj.asInstanceOf[Similar[H1, H2]]

  implicit val similarHNil: Similar[HNil, HNil] = create[HNil, HNil]

  implicit def similarCons[T1, T2, H1 <: HList, H2 <: HList](
    implicit ev: Similar[H1, H2]
  ): Similar[T1 :: H1, T2 :: H2] = create[T1 :: H1, T2 :: H2]


  implicit val similarCNil: Similar[CNil, CNil] = create[CNil, CNil]

  implicit def similarCl[T1, T2, C1 <: Coproduct, C2 <: Coproduct]: Similar[T1 :+: C1, T2 :+: C2] =
    create[T1 :+: C1, T2 :+: C2]
}
