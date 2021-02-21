package org.example.code_generation.examples5

import shapeless.<:!<
import shapeless.exprs.Cached2

case class Maybe[T](v: Option[T]) {
  def getOrElse(default: => T): T = v.getOrElse(default)
}

trait WithMaybe[Mode, Discriminant] {

  implicit def onlyOne[T](
    implicit ev: Cached2[Mode <:< Discriminant]
  ): Maybe[T] = Maybe(None)

  implicit def onlyOneOk[T](
    implicit ev: Cached2[Mode <:!< Discriminant],
    e: Cached2[Option[T]]
  ): Maybe[T] = Maybe(e.value)

}
