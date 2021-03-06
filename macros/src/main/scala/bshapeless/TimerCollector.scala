package bshapeless

import scala.collection.mutable

class TimerCollector {

  protected var sum: Long = 0

  private val m = mutable.AnyRefMap.empty[String, BigDecimal]
  private val unit = mutable.AnyRefMap.empty[String, String]

  private val timeUnit = "μs"

  def timer[T](key: String)(f: => T): T = {
    val s = System.nanoTime()
    val r = f
    val tL = System.nanoTime() - s
    val t: BigDecimal = tL
    sum += tL
    m.updateWith(key)(_.map(_ + t/1000D).orElse(Some(t/1000D)))
    unit.getOrElseUpdate(key, timeUnit)
    r
  }

  def tick(key: String, value: BigDecimal = 1): Unit = {
    m.updateWith(key)(_.map(_ + value) orElse Some(value))
    unit.getOrElseUpdate(key, "ticks")
  }

  def set(key: String, value: BigDecimal, unitM: String = "times"): Unit = {
    m.update(key, value)
    unit.getOrElseUpdate(key, unitM)
  }


  def printable: String = "Timer:\n" + (m.toList.sortBy(_._1).map(s => s"${s._1} - ${s._2} ${unit(s._1)}").mkString("\n"))
}
