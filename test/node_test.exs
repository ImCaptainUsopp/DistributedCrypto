defmodule DistributedCryptoTest do
  use ExUnit.Case
  alias DistributedCrypto.Node

  test "causal broadcast ensures consistent state across nodes" do
    :ok = LocalCluster.start()
    {:ok, cluster} = LocalCluster.start_link(3, prefix: "dsn-", applications: [:distributed_crypto])
    {:ok, [n1, n2, n3] = nodes} = LocalCluster.nodes(cluster)

    # Initialize all nodes with 0
    assert 0 = Node.get_value(n1)
    assert 0 = Node.get_value(n2)
    assert 0 = Node.get_value(n3)

    # Concurrent updates on different nodes
    Node.increment(n1)
    Node.increment(n2)
    Node.decrement(n3)

    # Wait for updates to propagate
    Process.sleep(500)

    # Retrieve values from all nodes
    value_n1 = Node.get_value(n1)
    value_n2 = Node.get_value(n2)
    value_n3 = Node.get_value(n3)

    # Verify causal consistency: all nodes must converge to the same final value
    assert value_n1 == value_n2


    # Verify the final state after concurrent operations
    # Incremented twice, decremented once: 0 + 1 + 1 - 1 = 1
    assert value_n1 == 1

    LocalCluster.stop(cluster)
  end
end
