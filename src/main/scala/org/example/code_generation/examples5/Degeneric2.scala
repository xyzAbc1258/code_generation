package org.example.code_generation.examples5

import shapeless._

import scala.reflect.api
import scala.reflect.api.TypeCreator
import scala.reflect.api.Universe
import scala.reflect.runtime
import scala.reflect.runtime.universe._

trait Degeneric2[H <: HList, F[_, _]] {
  type Out
  val tt: TypeTag[Out]
}

object Degeneric2 {

  implicit def tt[T: WeakTypeTag]: TypeTag[T] = null

  type Aux[H <: HList, F[_, _], O] = Degeneric2[H, F] {type Out = O}

  def apply[H <: HList, F[_, _]](
    implicit e: Degeneric2[H, F]
  ): Aux[H, F, e.Out] = e

  private def instance[H <: HList, F[_,_], O](t: TypeTag[O]): Aux[H, F, O] =
    new Degeneric2[H, F] {type Out = O; val tt = t}

  implicit def single[T, R, F[_,_]]/*(implicit tt: TypeTag[F[T,R]])*/: Aux[(T,R)::HNil,F, F[T,R]] = instance(null)

  implicit def cons[T, R, L <: HList, F[_,_]](
    implicit e: Degeneric2[L, F]//, t: TypeTag[F[T,R]]
  ):Aux[(T, R)::L, F, F[T, R] with e.Out] = {
    instance(/*TypeTag.apply(runtime.currentMirror,
      new TypeCreator {
        override def apply[U <: Universe with Singleton](m: api.Mirror[U]): U#Type =
          m.universe.internal.intersectionType(List(
            t.in(m).tpe.asInstanceOf[m.universe.Type],
            e.tt.in(m).tpe.asInstanceOf[m.universe.Type]
          ))
      }*/null
    )
  }
}
