package bshapeless

import shapeless.{HList, HNil}
import shapeless.ops.hlist.Selector

import scala.annotation.tailrec

trait SelectorWrapper[H <: HList, T] extends (H => T) {
  val index: Int

  def selector[H1 <: HList, R]: Selector[H1, R]

  override def equals(o: Any): Boolean =
    o match {
      case w: SelectorWrapper[_, _] if w.index == index => true
      case _ => false
    }

  override def hashCode(): Int = index

}

class SelectorWrapperImpl[H <: HList, T](val s: Selector[H, T]) extends SelectorWrapper[H, T] {

  val index = HListUtils.selectorIndex(s, 50)

  override def apply(v1: H): T = s(v1)

  override def selector[H1 <: HList, R]: Selector[H1, R] =
    s.asInstanceOf[Selector[H1, R]]
}

class SelectorWrapperIndexed[H <: HList, T](val index: Int) extends SelectorWrapper[H, T] {
  sw =>

  override def apply(v1: H): T = {
    @tailrec
    def select(h: HList, i: Int): T =
      h match {
        case x: shapeless.::[T@unchecked, HList] if i == 0 => x.head
        case x: shapeless.::[_, HList] => select(x.tail, i - 1)
        case nil: HNil => sys.error("Index greater than list length")
      }

    select(v1, index)
  }

  override def selector[H1 <: HList, R]: Selector[H1, R] =
    new Selector[H1, R] {
      override def apply(t: H1): R = sw(t.asInstanceOf[H]).asInstanceOf[R]
    }
}

object SelectorWrapper {

  implicit def wrap[H <: HList, T](s: Selector[H, T]): SelectorWrapper[H, T] =
    new SelectorWrapperImpl[H, T](s)

  def apply[H <: HList, T](n: Int): SelectorWrapper[H, T] = {
    new SelectorWrapperIndexed[H, T](n)
  }
}