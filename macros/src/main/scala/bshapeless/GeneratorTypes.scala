package bshapeless

trait GeneratorTypes {

  trait StructureTree
  object StructureTree {
    case object HNilTree extends StructureTree
    case class HListResult(head: StructureTree, tail: StructureTree) extends StructureTree

    case class CNilArg(tpe: String) extends StructureTree
    case class CoproductArgs(head: StructureTree, tail: StructureTree) extends StructureTree

    case class SelectArgs(n: Int) extends StructureTree

    case class FromArgsEq(tpe: String) extends StructureTree

    case class SelectCtx(n: Int) extends StructureTree

    case class Apply(fun: StructureTree, arg: StructureTree) extends StructureTree

    case class ApplyNative(name: String, arg: StructureTree) extends StructureTree

    case class Pair(first: StructureTree, second: StructureTree) extends StructureTree

    case class AbstractVal(inner: StructureTree) extends StructureTree

    case class AbstractFun(inner: StructureTree) extends StructureTree

    case class InlResult(inner: StructureTree) extends StructureTree

    case class InrResult(inner: StructureTree) extends StructureTree
  }
}
