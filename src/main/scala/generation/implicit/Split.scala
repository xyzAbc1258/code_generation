package generation.`implicit`

import shapeless._
import shapeless.ops.hlist.IsHCons
import shapeless.ops.hlist.Selector

trait Split[C <: HList, C1 <: HList, C2 <: HList] {
  i =>
  def c1(c: C): C1
  def c2(c: C): C2

  def selector[T, C1H](
    implicit ev: IsHCons[C1] {type H = C1H},
    c: C1H <:< T
  ): Selector[C, T] =
    new Selector[C, T] {
      override def apply(t: C): T = c1(t).head
    }

  def moveRight(implicit e: IsHCons[C1]): Split[C, e.T, e.H::C2] =
    new Split[C, e.T, e.H::C2] {
      override def c1(c: C): e.T = e.tail(i.c1(c))

      override def c2(c: C): e.H :: C2 = e.head(i.c1(c))::i.c2(c)
    }

  def moveLeft(implicit e: IsHCons[C2]): Split[C, e.H::C1, e.T] =
    new Split[C, e.H::C1, e.T] {
      override def c1(c: C): e.H :: C1 = e.head(i.c2(c))::i.c1(c)

      override def c2(c: C): e.T = e.tail(i.c2(c))
    }

  def mapLeft[NC1 <: HList](f: C1 => NC1): Split[C, NC1, C2] =
    new Split[C, NC1, C2] {
      override def c1(c: C): NC1 = f(i.c1(c))

      override def c2(c: C): C2 = i.c2(c)
    }

  def mapRight[NC2 <: HList](f: C2 => NC2): Split[C, C1, NC2] =
    new Split[C, C1, NC2] {
      override def c1(c: C): C1 = i.c1(c)

      override def c2(c: C): NC2 = f(i.c2(c))
    }

}

object Split {

  implicit def splitAll[C <: HList]: Split[C, C, HNil] =
    new Split[C, C, HNil] {
      override def c1(c: C): C = c
      override def c2(c: C): HNil = HNil
    }

  implicit def splitOne[H, T <: HList]: Split[H::T, T, H::HNil] =
    new Split[H::T, T, H::HNil] {
      override def c1(c: H :: T): T = c.tail
      override def c2(c: H :: T): H :: HNil = c.head :: HNil
    }

  implicit def splitMove2[C <: HList, H1, H2, C1 <: HList, C2 <: HList](
    implicit e: Split[C, H1::H2::C1, C2]
  ):Split[C, C1, H2::H1::C2] = e.moveRight.moveRight

}
