defmodule DistributedCrypto.Rest do
  @moduledoc """
  This module defines a REST API for the DistributedCrypto application.
  """
  use Plug.Router
  plug(Plug.Logger)
  plug(:match)

  plug(Plug.Parsers,
    parsers: [:json],
    pass: ["application/json"],
    json_decoder: Jason
  )

  plug(:dispatch)

  # Call it as:
  # curl http://localhost:8080/ && echo
  get "/" do
    respond_value_json(conn)
  end

  # Call it as:
  # curl -X PUT http://localhost:8080/increment && echo
  put "/increment" do
    DistributedCrypto.Node.increment()
    respond_value_json(conn)
  end

  # Call it as:
  # curl -X PUT http://localhost:8080/decrement && echo
  put "/decrement" do
    DistributedCrypto.Node.decrement()
    respond_value_json(conn)
  end

  # Fallback handler when there was no match
  match _ do
    send_resp(conn, 404, "Not Found")
  end

  defp respond_value_json(conn) do
    {:ok, value} = DistributedCrypto.Node.get_value()
    send_resp(conn, 200, Jason.encode!(%{"value" => value}))
  end
end
