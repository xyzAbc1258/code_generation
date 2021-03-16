package bshapeless

import scala.annotation.tailrec

trait FunctionProviders extends CommonUtils {

  import u._

  trait Indexed[T] {
    def idx: Int

    def subIndex: Int

    def withIndex(n: Int): T

    def incIdx(): T = withIndex(idx + 1)
  }

  sealed trait Func extends Indexed[Func] {

    def args: Seq[Type]

    def result: Type

    def wholeTypeTree: Tree = TypeTree(wholeType)

    def wholeType: Type
  }

  case class SimpleFunc1(arg: Type, result: Type, idx: Int, subIndex: Int) extends Func {
    val args: Seq[Type] = Seq(arg)

    override def withIndex(n: Int): SimpleFunc1 = copy(idx = n)

    override val wholeType: Type = arg ==> result
  }

  case class ComplexFunc(arg: Type, inner: Func, idx: Int, subIndex: Int) extends Func {
    val args: Seq[Type] = arg +: inner.args

    def result: Type = inner.result

    override def withIndex(n: Int): ComplexFunc = copy(inner = inner.withIndex(n), idx = n)

    override val wholeType: Type = arg ==> inner.wholeType
  }

  case class ObjectFunc(wholeType: Type, objType: Type, method: MethodSymbol, idx: Int) extends Func {
    val inner = {
      if (method.paramLists.flatten.nonEmpty) { // Currently only single param lists are supported. Just like in Func
        def buildT(args: List[List[Symbol]]): Type = args match {
          case List(s) :: tail => s.info ==> buildT(tail)
          case Nil => method.returnType
        }

        typeToFunc(buildT(method.paramLists), 0, 0).headOption
      } else None
    }

    override def args: Seq[Type] = objType +: inner.map(_.args).getOrElse(Nil)

    override def result: Type = inner.map(_.result).getOrElse(method.returnType)

    override def subIndex: Int = 0

    override def withIndex(n: Int): Func = copy(idx = n)

  }

  def typeToFunc(t: Type, idx: Int, subIndex: Int = 0): Seq[Func] = {
    t.dealias match {
      case Func1Extractor(arg, r@Func1Extractor(_, _)) =>
        Seq(ComplexFunc(arg, typeToFunc(r, idx).head, idx, subIndex))
      case Func1Extractor(arg, t) =>
        Seq(SimpleFunc1(arg, t, idx, subIndex))
      case RefinedType(inner, _) =>
        inner.toArray.zipWithIndex.flatMap { case (t, i) => typeToFunc(t, idx, i) }
      case t if t <:< Types.objectProviderTpe =>
        val tpe = t.firstTypeArg
        val methods = userMethods(tpe)
        log(s"Methods: ${methods.mkString("\n")}")
        methods.map(x => ObjectFunc(t, tpe, x, idx))
      case MethodType(_, tpe) => typeToFunc(tpe, idx, subIndex)
      case x => sys.error("Match error " + x + " " + showRaw(x))
    }
  }

  trait FuncProvider extends Indexed[FuncProvider] {
    def fittingFunction(expectedResult: Type, withSubtyping: Boolean): Option[Func]

    def wholeType: Type

    def name: Option[String]

    def withName(n: String): FuncProvider
  }

  case class SimpleFuncProvider(f: Func, name: Option[String] = None) extends FuncProvider {
    override def fittingFunction(expectedResult: Type, withSubtyping: Boolean): Option[Func] =
      Some(f).filter(x => if (!withSubtyping) x.result =:= expectedResult else x.result <:< expectedResult)

    override def wholeType: Type = f.wholeType

    override def idx: Int = f.idx

    override def subIndex: Int = f.subIndex

    override def withIndex(n: Int): FuncProvider = copy(f.withIndex(n))

    override def withName(n: String): FuncProvider = copy(name = Some(n))
  }

  case class GenericFuncProvider(wholeType: Type, symbols: Map[Type, Set[Type]], idx: Int, subIndex: Int, name: Option[String] = None) extends FuncProvider {
    private val genType = typeToFunc(wholeType, idx, subIndex).head

    private val (poly, polyMap) = toPolyType(wholeType)

    val polyBuilder = toFuncBuilder(polyMap.values.toSet, poly)

    def toPolyType(t: Type): (Type, Map[Type, Type]) = {

      val toSymbols = symbols.keySet.map(x => x -> x)
      val toReplace = toSymbols.flatMap(x => symbols(x._1).map(_ -> x._2))
      val repl = t.map(x => toReplace.find(_._1 =:= x).map(_._2).getOrElse(x))

      (repl, toSymbols.toMap)
    }

    def toFuncBuilder(s: Set[Type], t: Type): FuncBuilder = {
      t match {
        case Func1Extractor(a, r@Func1Extractor(_, _)) =>
          ComplexFuncBuilder(toTypeBuilder(s, a), toFuncBuilder(s, r))
        case Func1Extractor(a, r) =>
          SimpleFuncBuilder(toTypeBuilder(s, a), toTypeBuilder(s, r))
      }
    }

    def toTypeBuilder(s: Set[Type], t: Type): TypeBuilder = {
      val found = s.find(_ =:= t)
      found match {
        case Some(value) => Selector(value)
        case None =>
          if (t.typeArgs.nonEmpty)
            Apply(t.typeConstructor, t.typeArgs.map(toTypeBuilder(s, _)))
          else ConstType(t)
      }
    }

    sealed trait FuncBuilder {
      def buildFunc(f: Map[Type, Type]): Func
    }

    case class SimpleFuncBuilder(argBuilder: TypeBuilder, resBuilder: TypeBuilder) extends FuncBuilder {
      override def buildFunc(f: Map[Type, Type]): Func =
        SimpleFunc1(argBuilder.build(f), resBuilder.build(f), idx, subIndex)
    }

    case class ComplexFuncBuilder(argBuilder: TypeBuilder, innerBuilder: FuncBuilder) extends FuncBuilder {
      override def buildFunc(f: Map[Type, Type]): Func =
        ComplexFunc(argBuilder.build(f), innerBuilder.buildFunc(f), idx, subIndex)
    }

    sealed trait TypeBuilder {
      def build(m: Map[Type, Type]): Type
    }

    case class Selector(s: Type) extends TypeBuilder {
      override def build(m: Map[Type, Type]): Type = m(s)
    }

    case class ConstType(t: Type) extends TypeBuilder {
      override def build(m: Map[Type, Type]): Type = t
    }

    case class Apply(tyCon: Type, builders: List[TypeBuilder]) extends TypeBuilder {
      override def build(m: Map[Type, Type]): Type =
        appliedType(tyCon, builders.map(_.build(m)))
    }

    @tailrec
    private def compareSingle(s: Seq[Type], top: Seq[(Type, Type)], cm: Map[Type, Type]): Map[Type, Type] = {
      top match {
        case Seq() => cm
        case (pt, e) +: t =>
          val pta = pt.typeArgs
          val ea = e.typeArgs
          if (pta.nonEmpty && ea.nonEmpty) {
            if (pt.typeConstructor =:= e.typeConstructor) compareSingle(s, pta.map(_.dealias).zip(ea.map(_.dealias)) ++: t, cm)
            else compareSingle(s, t, cm)
          } else {
            val cn = s.filter(pt <:< _).map(_ -> e)
            val nc = cm ++ cn
            if (nc.size == s.size) nc
            else compareSingle(s, t, nc)
          }
      }
    }


    override def fittingFunction(expectedResult: Type, withSubtyping: Boolean): Option[Func] = {
      val cand = compareSingle(symbols.keys.toList, Seq((genType.result.dealias, expectedResult.dealias)), Map.empty)
      if (cand.size != symbols.size) return None

      val m = cand.map(x => polyMap(x._1) -> x._2)
      val gf = polyBuilder.buildFunc(m)
      //log(s"Generic candidate. cands: $cand exp: $expectedResult, got:  ${gf.result}")
      Some(gf).filter(x => if (!withSubtyping) x.result =:= expectedResult else x.result <:< expectedResult)
    }

    override def withIndex(n: Int): FuncProvider = copy(idx = n)

    override def withName(n: String): FuncProvider = copy(name = Some(n))
  }

}
