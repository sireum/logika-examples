import mill._, scalalib._

object `logika-examples` extends RootModule with ScalaModule {
  def scalaVersion = "2.13.15"
  def ivyDeps = Agg(
    ivy"org.sireum.kekinian::library:f6e1efff3a"
  )
  def repositoriesTask = T.task { super.repositoriesTask() :+ coursier.maven.MavenRepository("https://jitpack.io") }
}
