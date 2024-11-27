defmodule DistributedCrypto do
  @moduledoc """
  Documentation for DistributedCrypto.
  """

  use Application

  def start(_start_mode, _start_arg) do
   DistributedCrypto.Sup.start_link()
  end
end
