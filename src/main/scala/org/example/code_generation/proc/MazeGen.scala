package org.example.code_generation.proc

object MazeGen {

  def writeMaze(a: Array[Array[Boolean]]): Unit = {
    for(a <- a) {
      for(s <- a) {
        if(s) print(" ")
        else print("X")
      }
      println("|")
    }
  }

  def genNat(from: Int, to: Int, succS: String, zS: String): String = {
    if(from > to) return ""
    if(from == 0) return s"type _0 = $zS\n${genNat(from + 1, to, succS, zS)}"
    s"type _$from = $succS[_${from - 1}]\n${genNat(from + 1, to, succS, zS)}"
  }

  def main(args: Array[String]): Unit = {
    //println(genMaze(30, free.flatten, "P"))
    //println(genNat(23, 80, "shapeless.Succ", "Z"))
    //println(fromFile("./mtext.txt", "P"))
    writeMaze(free)
  }

  def genMaze(rowsC: Int, arr: Array[Array[Boolean]], pairS: String): String = {
    def makep(r: Int, c: Int): String = s"$pairS[_$r, _$c]"
    arr.zipWithIndex.flatMap{
      case (rowb, r) => rowb.zipWithIndex.map{case (v, c) => v -> makep(r, c)}
    }.filter(_._1).map(_._2).mkString("::") ++ "::HNil"
  }

  def fromFile(path: String, pairS: String): String = {
    val s = scala.io.Source.fromFile(path, "UTF-8")
    val lines = s.getLines().filterNot(_.isEmpty).toList
    s.close()
    val woEnd = lines.map(_.replace("|", ""))
    val arr = lines.map(_.map(_ != 'X').toArray).toArray
    genMaze(woEnd.head.length, arr, pairS)
  }

  val free: Array[Array[Boolean]] = {
    val arr = Array[Array[Boolean]](
      Array(true, false, true, true, true, true, true, false, true, true, true,
        true, true, false, true, false, true, true, true, false, true, true,
        true, false, true, true, true, false, true, true),
      Array(true, true, true, true, true, true, true, true, true, false, true,
        false, false, true, true, false, false, true, true, true, true, true,
        true, true, true, true, false, false, false, true),
      Array(true, true, true, true, true, true, true, false, true, false, true,
        true, true, true, false, true, true, true, true, true, false, false,
        true, true, false, true, true, false, true, false),
      Array(true, true, true, true, true, false, true, true, false, false, true,
        true, true, true, true, true, true, true, true, true, true, true, true,
        true, false, true, true, true, true, false),
      Array(true, true, true, true, true, false, true, true, false, false, true,
        false, true, false, true, true, false, true, true, true, true, true,
        true, false, true, true, true, true, true, false),
      Array(true, true, false, false, true, true, true, true, false, true, true,
        true, true, true, false, true, true, true, false, true, true, true,
        true, true, false, true, true, true, true, true),
      Array(true, true, true, false, true, false, false, true, true, false,
        true, true, true, false, true, true, true, true, true, true, true, true,
        true, true, true, true, true, true, true, true),
      Array(true, true, true, false, true, false, false, true, true, false,
        false, false, true, true, true, true, false, true, true, true, false,
        true, true, true, true, false, true, true, false, true),
      Array(true, true, true, false, true, true, false, true, true, false, true,
        false, true, true, false, false, false, true, false, true, true, true,
        true, true, false, false, true, false, true, true),
      Array(true, false, false, true, true, true, true, true, true, true, true,
        true, false, true, true, true, false, true, true, true, true, true,
        true, true, false, false, true, false, true, true),
      Array(true, false, true, false, true, true, false, true, true, true, true,
        true, true, true, true, false, true, true, true, false, true, false,
        true, false, true, true, false, false, true, false),
      Array(true, true, true, false, true, true, true, true, true, false, true,
        true, true, true, true, false, true, true, false, false, true, false,
        true, true, true, true, true, true, true, true),
      Array(true, false, true, true, false, false, true, false, false, true,
        true, true, false, true, true, true, true, true, false, true, true,
        true, true, true, true, true, true, true, true, true),
      Array(true, true, true, false, true, true, false, true, true, true, true,
        true, true, true, true, true, false, true, true, true, true, true, true,
        true, true, true, false, true, true, true),
      Array(false, true, true, false, true, true, false, true, true, true, true,
        true, false, true, true, false, true, true, true, false, true, true,
        true, false, true, true, true, true, true, true),
      Array(true, false, false, true, true, true, false, false, true, true,
        false, false, true, true, false, true, true, false, false, true, true,
        true, true, true, true, true, false, true, true, true),
      Array(true, true, false, false, true, true, true, true, true, true, true,
        false, true, true, true, true, true, true, true, true, true, true, true,
        true, true, false, true, true, true, true),
      Array(true, true, true, true, true, true, true, true, true, true, false,
        false, true, true, true, false, false, false, true, false, true, true,
        true, true, true, true, true, true, true, true),
      Array(true, true, true, true, true, false, true, true, true, false, true,
        false, false, true, true, true, true, true, false, true, true, true,
        true, true, true, true, true, false, false, true),
      Array(false, false, true, true, false, true, false, true, true, false,
        false, true, false, true, true, true, true, true, true, true, true,
        true, true, true, true, false, true, true, true, true),
      Array(true, true, true, false, false, false, true, false, true, true,
        true, true, true, false, true, true, true, true, true, true, true, true,
        false, true, false, true, true, true, true, false),
      Array(false, true, true, true, true, true, true, true, true, true, true,
        false, true, true, true, true, true, true, true, true, true, true, true,
        true, true, false, true, false, false, true),
      Array(true, true, true, true, true, false, true, true, true, true, true,
        true, true, true, false, true, false, true, true, false, true, true,
        true, true, true, true, true, true, true, true),
      Array(true, true, true, false, true, true, true, true, false, true, true,
        false, true, true, true, true, true, false, true, true, false, true,
        true, true, true, false, true, false, true, true),
      Array(true, true, true, true, true, true, true, false, true, true, true,
        true, true, true, true, true, true, false, true, true, true, true, true,
        true, true, false, false, true, true, true),
      Array(true, true, true, false, true, true, false, true, true, true, true,
        false, true, true, true, true, true, true, false, false, true, true,
        true, true, false, true, true, true, false, true),
      Array(false, false, true, true, false, true, true, true, true, false,
        true, true, true, false, true, true, false, false, true, true, true,
        true, true, true, true, true, false, false, false, true),
      Array(true, true, true, true, true, true, true, false, true, false, true,
        false, true, false, true, true, false, false, false, true, true, true,
        true, true, true, true, true, true, true, true),
      Array(true, true, false, true, false, true, true, true, true, true, false,
        true, true, true, true, true, false, true, true, false, false, true,
        false, true, false, true, true, false, true, true),
      Array(true, true, true, true, true, false, true, true, false, false,
        false, true, true, false, false, true, false, false, true, true, true,
        false, true, true, true, true, true, true, true, true)
    )
    arr
  }
}
