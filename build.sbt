Global / semanticdbEnabled := true

lazy val root = project
  .in(file("."))
  .settings(
    name := "alabast",
    version := "0.1.0",
    scalaVersion := "3.0.0-M1",
    libraryDependencies ++= Seq(
      "org.scalameta" %% "munit" % "0.7.17" % Test
    ),
    testFrameworks += new TestFramework("munit.Framework"),
    Test / parallelExecution := false
  )
