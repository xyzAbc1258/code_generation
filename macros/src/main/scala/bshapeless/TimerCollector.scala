package bshapeless

import scala.collection.mutable

class TimerCollector {

  private val m = mutable.AnyRefMap.empty[String, Float]
  private val unit = mutable.AnyRefMap.empty[String, String]

  private val timeUnit = "μs"

  @inline def timer[T](key: String)(f: => T): T = {
    val s = System.nanoTime()
    val r = f
    val tL = System.nanoTime() - s
    val t: Float = tL
    m.updateWith(key)(_.map(_ + t/1000F).orElse(Some(t/1000F)))
    unit.getOrElseUpdate(key, timeUnit)
    r
  }

  @inline def tickReturn[T](key: String, value: Float = 1)(t: T): T = {
    tick(key, value)
    t
  }

  def tick(key: String, value: Float = 1): Unit = {
    m.updateWith(key)(_.map(_ + value) orElse Some(value))
    unit.getOrElseUpdate(key, "ticks")
  }

  def set(key: String, value: Float, unitM: String = "times"): Unit = {
    m.update(key, value)
    unit.getOrElseUpdate(key, unitM)
  }


  def printable: String = "Timer:\n" + (m.toList.sortBy(_._1).map(s => f"${s._1} - ${s._2}%1.3f ${unit(s._1)}").mkString("\n"))
}
