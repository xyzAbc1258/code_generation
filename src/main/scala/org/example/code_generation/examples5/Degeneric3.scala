package org.example.code_generation.examples5

import shapeless.{::, HList, HNil}

trait Degeneric3[H <: HList, F[_, _, _]] {
  type Out
}

object Degeneric3 {

  type Aux[H <: HList, F[_, _, _], O] = Degeneric3[H, F] {type Out = O}

  def apply[H <: HList, F[_, _, _]](
    implicit e: Degeneric3[H, F]
  ): Aux[H, F, e.Out] = e

  private def instance[H <: HList, F[_,_, _], O]: Aux[H, F, O] =
    new Degeneric3[H, F] {type Out = O}

  implicit def single[T, R, S, F[_,_, _]]: Aux[(T,R, S)::HNil,F, F[T,R,S]] = instance

  implicit def cons[T, R, S, L <: HList, F[_,_,_]](
    implicit e: Degeneric3[L, F]
  ):Aux[(T, R, S)::L, F, F[T, R, S] with e.Out] = instance
}

