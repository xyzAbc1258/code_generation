package org.example.code_generation.examples5

import shapeless._

/**
 * Trait creating intersection type from list of arguments and type constructor
 *
 * eg. Degeneric[Int::String::HNil, R => Option[R]].Out = (Int => Option[Int]) with (String => Option[String]).
 * @tparam H List of types
 * @tparam T Type constructor
 */
trait Degeneric1[H <: HList, T[_]] {
  type Out
}

object Degeneric1 {

  private val instance = new Degeneric1[Nothing, ({type T[R] = R})#T] {
    type Out = Nothing
  }

  type Aux[H <: HList, T[_], O] = Degeneric1[H, T] {type Out = O}

  implicit def single[T, F[_]]: Aux[T :: HNil, F, F[T]] = instance.asInstanceOf

  implicit def cons[T, R <: HList, F[_]](
    implicit e: Degeneric1[R, F]
  ): Aux[T :: R, F, F[T] with e.Out] =
    e.asInstanceOf

  def apply[T <: HList, F[_]](implicit e: Degeneric1[T, F]): Aux[T, F, e.Out] = e
}
