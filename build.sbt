val dottyVersion = "0.27.0-RC1"

Global / semanticdbEnabled := true

lazy val root = project
  .in(file("."))
  .settings(
    name := "alabast",
    version := "0.1.0",
    scalaVersion := dottyVersion,
    libraryDependencies ++= Seq(
      "org.scalameta" %% "munit" % "0.7.14" % Test
    ),
    testFrameworks += new TestFramework("munit.Framework"),
    Test / parallelExecution := false
  )
