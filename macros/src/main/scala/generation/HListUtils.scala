package generation

import shapeless.{HList, HNil}
import shapeless.ops.hlist.Selector

object HListUtils {

  def unsafeCollect[T](h: HList): List[T] = {
    h match {
      case cons: shapeless.::[T, HList] => cons.head :: unsafeCollect(cons.tail)
      case _: HNil => Nil
    }
  }

  def selectorIndex(s: Selector[_, _], max: Int): Int = {
    val l = Range(0, max).foldRight[HList](HNil)(_ :: _)
    s.asInstanceOf[Selector[HList, Int]](l)
  }

  def toHList(l: List[Any]): HList = {
    l.foldRight[HList](HNil)(_ :: _)
  }

}
