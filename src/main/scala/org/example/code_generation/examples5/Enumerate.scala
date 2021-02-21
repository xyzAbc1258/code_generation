package org.example.code_generation.examples5

case class Enumerate[T](values: Set[T]) {
  def map[R](f: T => R): Enumerate[R] = new Enumerate(values.map(f))

  def flatMap[R](f: T => Enumerate[R]): Enumerate[R] =
    new Enumerate(values.map(f).flatMap(_.values))

  def foreach[U](f: T => U): Unit = {
    values.foreach(f)
  }

  def ++[U >: T](e: Enumerate[U]): Enumerate[U] = {
    Enumerate(e.values ++ values)
  }

  def ++[U >: T](s: Set[U]): Enumerate[U] = {
    Enumerate(values ++ s)
  }
}

object Enumerate {

  def empty[T]: Enumerate[T] = Enumerate(Set.empty)

  def single[T](s: T): Enumerate[T] = new Enumerate[T](Set(s))

}