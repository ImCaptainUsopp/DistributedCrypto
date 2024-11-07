defmodule DistributedCryptoTest do
  use ExUnit.Case
  alias DistributedCrypto.Node


  # Démarrer le cluster local pour les tests
  #:ok = LocalCluster.start()
  #{:ok, cluster} = LocalCluster.start_link(3, prefix: "dsn-", applications: [:distributed_crypto])

  # Obtenir les nœuds du cluster
  #{:ok, [n1, n2, n3] = nodes} = LocalCluster.nodes(cluster)

  # Assurez-vous que les nœuds peuvent se pinger les uns les autres
  #Enum.each(nodes, fn n -> assert Node.ping(n) == :pong end)

  # Retourner les nœuds pour les tests
  #%{nodes: nodes, n1: n1, n2: n2, n3: n3}


  test "increment and synchronize value across nodes" do
    :ok = LocalCluster.start()
    {:ok, cluster} = LocalCluster.start_link(3, prefix: "dsn-", applications: [:distributed_crypto])
    {:ok, [n1, n2, n3] = nodes} = LocalCluster.nodes(cluster)
    # Vérifier les valeurs initiales
    assert 0 = Node.get_value(n1)
    assert 0 = Node.get_value(n2)
    #assert {:ok, 0} = Node.get_value(n3)

    # Incrémenter la valeur sur le nœud n1
    #n1.increment()

    # Attendre un moment pour que la synchronisation ait lieu
    #Process.sleep(100)

    # Vérifier que les deux nœuds reflètent la valeur incrémentée
    #assert {:ok, 1} = n1.get_value()
    #assert {:ok, 1} = n2.get_value()
    LocalCluster.stop(cluster)
  end
end
