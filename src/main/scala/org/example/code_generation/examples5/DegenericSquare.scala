package org.example.code_generation.examples5

import shapeless._

trait DegenericSquare[H1 <: HList, H2 <: HList, F[_, _]] {
  type Out
}

object DegenericSquare {

  type Aux[H1 <: HList, H2 <: HList, F[_, _], O] = DegenericSquare[H1, H2, F] {type Out = O}

  private def instance[H1 <: HList, H2 <: HList, F[_, _], O]: Aux[H1, H2, F, O] =
    new DegenericSquare[H1, H2, F] {type Out = 0}

  implicit def singleE[H1 <: HList, A, F[_, _]](
    implicit e: Degeneric1[H1, ({type X[B] = F[B, A]})#X]
  ): Aux[H1, A :: HNil, F, e.Out] = instance

  implicit def cons[H1 <: HList, A, R <: HList, F[_,_]](
    implicit e1: DegenericSquare[H1, R, F],
    e2: Degeneric1[H1, ({type X[B] = F[B, A]})#X]
  ): Aux[H1, A :: R, F, e2.Out with e1.Out] = instance

  def apply[H1 <: HList, H2 <: HList, F[_,_]](implicit e: DegenericSquare[H1, H2, F]): Aux[H1, H2, F, e.Out] = e
}