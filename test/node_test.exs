defmodule DistributedCryptoTest do
  use ExUnit.Case
  alias DistributedCrypto.Node

  @timeout 5000
  @poll_interval 100
  @poll_delay 50

  test "causal broadcast ensures consistent state across nodes" do
    # Initialize LocalCluster for 3 nodes
    :ok = LocalCluster.start()
    {:ok, cluster} = LocalCluster.start_link(3, prefix: "dsn-", applications: [:distributed_crypto])
    {:ok, [n1, n2, n3] = nodes} = LocalCluster.nodes(cluster)

    # Initial values of all nodes should be 0
    assert Node.get_value(n1) == 0
    assert Node.get_value(n2) == 0
    assert Node.get_value(n3) == 0

    # Perform concurrent updates on the nodes
    Node.increment(n1)
    Node.increment(n2)
    Node.decrement(n3)

    # Wait for updates to propagate across the cluster
    Process.sleep(10000)

    # Retrieve the final values from all nodes
    value_n1 = Node.get_value(n1)
    value_n2 = Node.get_value(n2)
    value_n3 = Node.get_value(n3)

    # Check that the nodes are consistent and converge to the same value
    assert value_n1 == value_n2
    assert value_n2 == value_n3

    # Verify the final state after the operations:
    # Incremented twice, decremented once: (0 + 1 + 1 - 1) = 1
    assert value_n1 == 1

    # Ensure that the vector clocks have been updated correctly
    # You can assert specific values in the vector clock if needed, but this depends on how you expose vector clocks.
    # For instance:
    # assert Node.get_vector_clock(n1) == Node.get_vector_clock(n2)
    # assert Node.get_vector_clock(n2) == Node.get_vector_clock(n3)

    # Stop the cluster after the test is completed
    LocalCluster.stop(cluster)
  end
end
