package org.example.code_generation.examples5

object ListOps {

  trait Attrs
  trait Filtered extends Attrs
  trait Sorted extends Attrs
  trait All extends Attrs
  trait Exists extends Attrs

  trait Sorter extends Attrs
  trait Filter extends Attrs

  trait Zero extends Attrs

  implicit class Tag[T](t: T) {
    def tag[R <: Attrs]: T with R = t.asInstanceOf[T with R]
  }

  type TFilter[T, R] = List[T] => ((T => Boolean) with Filter with R) => (List[T] with Filtered with R)

  def filter[T, R](l: List[T])(f: (T => Boolean) with Filter with R): List[T] with Filtered with R =
    l.filter(f).tag[Filtered].asInstanceOf[List[T] with Filtered with R]

  type TFind[T] = List[T] => ((T => Boolean) with Filter) => (Option[T] with Filtered)

  def find[T](l: List[T])(f: (T => Boolean) with Filter): Option[T] = l.find(f)

  type TFold[T, R] = List[T] => (R with Zero) => (R => T => R) => R

  def fold[T, R](l: List[T])(z: R with Zero)(x: R => T => R): R = {
    l.foldLeft[R](z)((a, b) => x(a)(b))
  }

  type TSort[T] = List[T] => ((T => Int) with Sorter) => (List[T] with Sorted)

  def sortByInt[T](l: List[T])(f: (T => Int) with Sorter): List[T] with Sorted =
    l.sortBy(f).tag[Sorted]

  type TAll[T] = List[T] => (T => Boolean) => (Boolean with All)

  def forall[T](l: List[T])(f: T => Boolean): Boolean with All =
    l.forall(f).tag[All]

  type TExists[T] = List[T] => (T => Boolean) => (Boolean with Exists)

  def exists[T](l: List[T])(f: T => Boolean): Boolean with Exists =
    l.forall(f).tag[Exists]

  type TMap[T, R] = List[T] => (T => R) => List[R]

  def map[T, R](l: List[T])(f: T => R): List[R] = l.map(f)

  type TFlatMap[T, R] = List[T] => (T => List[R]) => List[R]

  def flatMap[T, R](l: List[T])(f: T => List[R]): List[R] = l.flatMap(f)

  type TSingle[T] = T => List[T]

  def single[T](e: T): List[T] = List(e)

}
