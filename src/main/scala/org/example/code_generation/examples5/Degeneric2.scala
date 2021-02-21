package org.example.code_generation.examples5

import shapeless._

trait Degeneric2[H <: HList, F[_, _]] {
  type Out
}

object Degeneric2 {

  type Aux[H <: HList, F[_, _], O] = Degeneric2[H, F] {type Out = O}

  def apply[H <: HList, F[_, _]](
    implicit e: Degeneric2[H, F]
  ): Aux[H, F, e.Out] = e

  private def instance[H <: HList, F[_,_], O]: Aux[H, F, O] =
    new Degeneric2[H, F] {type Out = O}

  implicit def single[T, R, F[_,_]]: Aux[(T,R)::HNil,F, F[T,R]] = instance

  implicit def cons[T, R, L <: HList, F[_,_]](
    implicit e: Degeneric2[L, F]
  ):Aux[(T, R)::L, F, F[T, R] with e.Out] = instance
}
