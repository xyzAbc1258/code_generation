package generation

import scala.annotation.tailrec

trait FunctionProviders extends CommonUtils {

  import u._

  trait Indexed[T] {
    def idx: Int

    def subIndex: Int

    def withIndex(n: Int): T

    def incIdx(): T = withIndex(idx + 1)
  }

  trait IndexedProvider {
    protected def idxProvider: Indexed[_]

    def idx: Int = idxProvider.idx

    def subIndex: Int = idxProvider.subIndex
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

  case class ObjectFunc(wholeType: Type, objType: Type, method: MethodSymbol, inner: Option[Func], idx: Int) extends Func {

    private def methodRealType: Type = method.returnType.asSeenFrom(objType, objType.typeSymbol)

    override def args: Seq[Type] = objType +: inner.map(_.args).getOrElse(Seq.empty)

    override def result: Type = inner.map(_.result).getOrElse(methodRealType)

    def resultFuncType:Type = inner.map(_.wholeType).getOrElse(methodRealType)

    override def subIndex: Int = 0

    override def withIndex(n: Int): Func = copy(idx = n)

  }

  object ObjectFunc {

    def buildFuncFromMethod(objType: Type, m: MethodSymbol, idx: Int): Seq[Func] = {
      //in case function is generic and we have specified type which arise from object type
      def inObjView(t: Type): Type = t.asSeenFrom(objType, objType.typeSymbol)
      def buildT(args: List[List[Symbol]]): Seq[Func] = args match {
        case List(s) :: (tail@_ :: _) => Seq(ComplexFunc(inObjView(s.info), buildT(tail).ensuring(_.size == 1).head, idx, 0))
        case List(s) :: Nil => Seq(SimpleFunc1(inObjView(s.info), inObjView(m.returnType), idx, 0))
      }
      if(m.paramLists.nonEmpty) buildT(m.paramLists)
      else {
        m.returnType match {
          case RefinedType(types, _) => //def refinedFunc: (A => B) with (C => D)
            types.collect{case f@Func1Extractor(_, _) => f}
              .zipWithIndex
              .flatMap{case (f,i) => typeToFunc(inObjView(f), idx, i)}
          case _ => Nil
        }
      }
    }

    def apply(wholeType: Type, objType: Type, method: MethodSymbol, idx: Int): Seq[ObjectFunc] = {
      val built = buildFuncFromMethod(objType, method, idx)
      if(built.nonEmpty) built.map { f => new ObjectFunc(wholeType, objType, method, Some(f), idx) }
      else ObjectFunc(wholeType, objType, method, None, idx) :: Nil
    }
  }

  def typeToFunc(t: Type, idx: Int, subIndex: Int = 0): Seq[Func] = {
    t.dealias match {
      case Func1Extractor(arg, r@Func1Extractor(_, _)) =>
        Seq(ComplexFunc(arg, typeToFunc(r, idx).head, idx, subIndex))
      case Func1Extractor(arg, t) =>
        Seq(SimpleFunc1(arg, t, idx, subIndex))
      case RefinedType(inner, _) =>
        inner.toArray.zipWithIndex.flatMap { case (t, i) => typeToFunc(t, idx, i) }
      case x => sys.error("Match error " + x + " " + showRaw(x))
    }
  }

  trait FuncProvider extends Indexed[FuncProvider] {

    protected def isSuitable(typ: Type, expectedType: Type, withSubtyping: Boolean): Boolean =
      if(withSubtyping) typ <:< expectedType else typ =:= expectedType

    def fittingFunction(expectedResult: Type, withSubtyping: Boolean): Option[Func]

    def wholeType: Type

    def name: Option[String]

    def withName(n: String): FuncProvider
  }

  case class SimpleFuncProvider(f: Func, name: Option[String] = None) extends FuncProvider {
    override def fittingFunction(expectedResult: Type, withSubtyping: Boolean): Option[Func] =
      Some(f).filter(x => isSuitable(x.result, expectedResult, withSubtyping))

    override def wholeType: Type = f.wholeType

    override def idx: Int = f.idx

    override def subIndex: Int = f.subIndex

    override def withIndex(n: Int): FuncProvider = copy(f.withIndex(n))

    override def withName(n: String): FuncProvider = copy(name = Some(n))
  }

  case class GenericFuncProvider(polyFunc: PolyFunc, name: Option[String]) extends FuncProvider with IndexedProvider {
    @tailrec
    private def compareSingle(s: Seq[Type], top: Seq[(Type, Type)], cm: Map[Type, Type]): Map[Type, Type] = {
      top match {
        case Seq() => cm
        case (RefinedType(ptp, _), RefinedType(ep,_ )) +: t if ptp.length == ep.length =>
          compareSingle(s, ptp.map(_.dealias).zip(ep.map(_.dealias)) ++: t, cm)
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

    override def fittingFunction(expectedResult: Type, withSubtyping: Boolean): Option[Func] = Timer.timer("generic provider time") {
      Timer.tick("Generic fitting call")
      val candidateTypeArgs = compareSingle(polyFunc.typeArgs, Seq((polyFunc.retTypeTemplate.dealias, expectedResult.dealias)), Map.empty)
      if (candidateTypeArgs.size != polyFunc.typeArgs.size) return None
      val m = polyFunc.typeArgs.map(candidateTypeArgs)
      val gf = polyFunc.withTypeArgs(m)
      Option.when(isSuitable(gf.result, expectedResult, withSubtyping))(gf)
    }

    override def withIndex(n: Int): FuncProvider = copy(polyFunc = polyFunc.withIndex(n))

    override def withName(n: String): FuncProvider = copy(name = Some(n))

    override def wholeType: u.Type = polyFunc.wholeType

    override protected def idxProvider: Indexed[_] = polyFunc
  }

  object GenericFuncProvider {

    def apply(wholeType: Type, symbols: Map[Type, Set[Type]], idx: Int, subIndex: Int, name: Option[String] = None): GenericFuncProvider = {
      new GenericFuncProvider(
        FreePolyFunc(wholeType, symbols, idx, subIndex),
        name
      )
    }

    def apply(wholeType: Type, objType: Type, method: MethodSymbol, idx: Int, subIndex: Int): GenericFuncProvider = {
      new GenericFuncProvider(
        ObjectPolyFunc(wholeType, objType, method, idx, subIndex),
        Some(method.name.decodedName.toString)
      )
    }
  }


  trait PolyFunc extends Indexed[PolyFunc] {
    def retTypeTemplate: Type

    def typeArgs: Seq[Type]

    def withTypeArgs(args: Seq[Type]): Func

    def wholeType: Type

    protected def toFuncBuilder(s: Set[Type], t: Type, keyMap: Map[Type, Int]): FuncBuilder = {
      t match {
        case Func1Extractor(a, r@Func1Extractor(_, _)) =>
          ComplexFuncBuilder(toTypeBuilder(s, a, keyMap), toFuncBuilder(s, r, keyMap))
        case Func1Extractor(a, r) =>
          SimpleFuncBuilder(toTypeBuilder(s, a, keyMap), toTypeBuilder(s, r, keyMap))
      }
    }

    protected def toTypeBuilder(s: Set[Type], t: Type, keyMap: Map[Type, Int]): TypeBuilder = {
      val found = s.find(_ =:= t)
      found match {
        case Some(value) => Selector(keyMap(value))
        case None if t.typeArgs.nonEmpty => Apply(t.typeConstructor, t.typeArgs.map(toTypeBuilder(s, _, keyMap)))
        case None =>
          t match {
            case RefinedType(t, _) => Refine(t.map(toTypeBuilder(s, _, keyMap)))
            case t => ConstType(t)
          }
      }
    }

    protected sealed trait FuncBuilder {
      def buildFunc(f: Map[Int, Type]): Func
    }

    protected case class SimpleFuncBuilder(argBuilder: TypeBuilder, resBuilder: TypeBuilder) extends FuncBuilder {
      override def buildFunc(f: Map[Int, Type]): Func = SimpleFunc1(argBuilder.build(f), resBuilder.build(f), idx, subIndex)
    }

    protected case class ComplexFuncBuilder(argBuilder: TypeBuilder, innerBuilder: FuncBuilder) extends FuncBuilder {
      override def buildFunc(f: Map[Int, Type]): Func = ComplexFunc(argBuilder.build(f), innerBuilder.buildFunc(f), idx, subIndex)
    }

    protected sealed trait TypeBuilder {
      def build(m: Map[Int, Type]): Type
    }

    protected case class Selector(s: Int) extends TypeBuilder {
      override def build(m: Map[Int, Type]): Type = m(s)
    }

    protected case class ConstType(t: Type) extends TypeBuilder {
      override def build(m: Map[Int, Type]): Type = t
    }

    protected case class Apply(tyCon: Type, builders: List[TypeBuilder]) extends TypeBuilder {
      override def build(m: Map[Int, Type]): Type = appliedType(tyCon, builders.map(_.build(m)))
    }

    protected case class Refine(builders: List[TypeBuilder]) extends TypeBuilder {
      override def build(m: Map[Int, Type]): Type = internal.intersectionType(builders.map(_.build(m)))
    }

  }

  case class FreePolyFunc(wholeType: Type, symbols: Map[Type, Set[Type]], idx: Int, subIndex: Int) extends PolyFunc {
    private lazy val genType = typeToFunc(wholeType, idx, subIndex).head

    private lazy val (poly, polyMap) = toPolyType(wholeType)

    private lazy val polyBuilder = toFuncBuilder(polyMap.values.toSet, poly, typeArgs.zipWithIndex.toMap)

    private def toPolyType(t: Type): (Type, Map[Type, Type]) = {
      val toSymbols = symbols.keySet.map(x => x -> x)
      val toReplace = toSymbols.flatMap(x => symbols(x._1).map(_ -> x._2))
      val repl = t.map(x => toReplace.find(_._1 =:= x).map(_._2).getOrElse(x))
      (repl, toSymbols.toMap)
    }

    override def retTypeTemplate: Type = genType.result

    override val typeArgs: Seq[Type] = symbols.keys.toSeq

    override def withTypeArgs(args: Seq[Type]): Func = {
      polyBuilder.buildFunc(args.zipWithIndex.map(_.swap).toMap)
    }

    override def withIndex(n: Int): PolyFunc = copy(idx = n)
  }

  case class ObjectPolyFunc(wholeType: Type, objType: Type, method: MethodSymbol, idx: Int, subIndex: Int) extends PolyFunc {
    private lazy val (genType, symbols): (Func, Seq[Type]) = {
      method.typeSignature match {
        case PolyType(symbols, _) => (ObjectFunc.buildFuncFromMethod(objType, method, idx).head, symbols.map(_.asType.toType))
        case x => sys.error(s"Wrong signature $x")
      }
    }

    private lazy val builder = toFuncBuilder(symbols.toSet, genType.wholeType, symbols.zipWithIndex.toMap)

    override def retTypeTemplate: u.Type = genType.result

    override def typeArgs: Seq[u.Type] = symbols

    override def withTypeArgs(args: Seq[Type]): Func = {
      val inner = builder.buildFunc(args.zipWithIndex.map(_.swap).toMap)
      new ObjectFunc(wholeType, objType, method, Some(inner), idx)
    }

    override def withIndex(n: Int): PolyFunc = copy(idx = n)
  }

}
