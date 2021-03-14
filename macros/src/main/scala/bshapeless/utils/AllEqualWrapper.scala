package bshapeless.utils

/*Class that doesnt care about content. Useful in case classes to not care about element*/
class AllEqualWrapper[T](val t: T) {

  override def hashCode(): Int = 0

  override def equals(o: Any): Boolean = o match {
    case _ : AllEqualWrapper[T]@unchecked => true
    case _ => false
  }
}

object AllEqualWrapper {
  def apply[T](t: T): AllEqualWrapper[T] = new AllEqualWrapper[T](t)
}
