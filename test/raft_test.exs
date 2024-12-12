defmodule RaftTest do
  use ExUnit.Case
  alias DistributedCrypto.Node

  test "election timeout triggers candidate role and vote requests" do
    :ok = LocalCluster.start()
    {:ok, cluster} = LocalCluster.start_link(3, prefix: "dsn-", applications: [:distributed_crypto])
    {:ok, [n1, n2, n3] = nodes} = LocalCluster.nodes(cluster)
    Node.launch_election_timeout(n1)
    Node.launch_election_timeout(n2)
    Node.launch_election_timeout(n3)
    Process.sleep(5000)
    state = Node.get_state(n1)
    assert Node.get_current_role(state) == :Follower
    state.votedFor == node()
    LocalCluster.stop(cluster)
  end
end
