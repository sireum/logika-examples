import mill._, scalalib._

object `logika-examples` extends RootModule with ScalaModule {
  def scalaVersion = "2.13.15"
  def ivyDeps = Agg(
    ivy"org.sireum.kekinian::library:4.20241015.9f71e14"
  )
  def repositoriesTask = T.task { super.repositoriesTask() :+ coursier.maven.MavenRepository("https://jitpack.io") }
}
