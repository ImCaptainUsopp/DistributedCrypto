defmodule DistributedCrypto.MixProject do
  use Mix.Project

  def project do
    [
      app: :distributed_crypto,
      version: "0.1.0",
      elixir: "~> 1.14",
      start_permanent: Mix.env() == :prod,
      deps: deps()
    ]
  end

  # Run "mix help compile.app" to learn about applications.
  def application do
    [
      extra_applications: [:logger],
      mod: {DistributedCrypto.App, []}
    ]
  end

  # Run "mix help deps" to learn about dependencies.
  defp deps do
    [
      {:syn, "~> 3.3.0"},
      {:plug_cowboy, "~> 2.7.2"},
      {:jason, "~> 1.4.4"},
      {:local_cluster, "~> 2.0", only: [:test]},
      {:vector_clock, "~> 0.1.0"}                     # implementation of clock_vectors
      # {:dep_from_hexpm, "~> 0.3.0"},
      # {:dep_from_git, git: "https://github.com/elixir-lang/my_dep.git", tag: "0.1.0"}
    ]
  end
end
