defmodule DistributedCrypto.BrokenNode do
  use GenServer
  require Logger

  ### State Definition


  # valeur, vecteur clock, message queue , défault 0, init et [] --> chose de base quand tu crée un noeud
  defmodule State do
    @enforce_keys [:value, :vector_clock, :message_queue, :nbMsg, :wasDelivered]
    defstruct value: 0, vector_clock: DistributedCrypto.VectorClock.new(), message_queue: [], nbMsg: 0, wasDelivered: MapSet.new()
    @type t() :: %__MODULE__{value: integer(), vector_clock: DistributedCrypto.VectorClock.t(), message_queue: [{DistributedCrypto.VectorClock.t(), integer()}], nbMsg: integer(), wasDelivered: MapSet.t()}
  end

  ### Interfaces

  @spec start_link() :: :ignore | {:error, any} | {:ok, pid}
  def start_link() do
    GenServer.start_link(__MODULE__, {}, name: __MODULE__)
  end

  @spec propose_value(new_value :: integer()) :: :ok
  def propose_value(new_value) do
    GenServer.cast(__MODULE__, {:propose_value, new_value})
  end

  @spec increment(node()) :: :ok
  def increment(node), do: GenServer.cast({__MODULE__, node}, :increment)

  @spec decrement(node()) :: :ok
  def decrement(node), do: GenServer.cast({__MODULE__, node}, :decrement)


  @spec increment() :: :ok
  def increment(), do: GenServer.cast(__MODULE__, :increment)

  @spec decrement() :: :ok
  def decrement(), do: GenServer.cast(__MODULE__, :decrement)

  @spec get_value() :: integer()
  def get_value() do
    GenServer.call(__MODULE__, :get_value)
  end

  @spec get_value(node()) :: integer()
  def get_value(node) do
    GenServer.call({__MODULE__, node}, :get_value)
  end


  ### Callbacks (appelés par l'utilisateur par les fonctions d'interface)

  @impl true
  def init(_) do
    Logger.info("#{node()} started and joined cluster.")
    {:ok, %State{value: 0, vector_clock: DistributedCrypto.VectorClock.new(), message_queue: [], nbMsg: 0, wasDelivered: MapSet.new()}}
  end

  @impl true
  def handle_call(:get_value, _from, %State{value: value} = state) do # synchrone
    {:reply, value, state}
  end

  @impl true
  def handle_cast(:increment, %State{value: value, vector_clock: vc, nbMsg: nbmsg} = state) do # asynchrone
    new_value = value + 1
    new_nbMsg = nbmsg + 1
    new_vector_clock = DistributedCrypto.VectorClock.increment_entry(vc, node())
    new_state = %State{state | value: new_value, vector_clock: new_vector_clock}
    reliable_broadcast(new_value, new_vector_clock, node(), new_nbMsg,  %State{wasDelivered: delivered} = state)
    {:noreply, new_state}
  end

  @impl true
  def handle_cast(:decrement, %State{value: value, vector_clock: vc, nbMsg: nbMsg} = state) do
    new_value = value - 1
    new_nbMsg = nbMsg + 1
    new_vector_clock = DistributedCrypto.VectorClock.increment_entry(vc, node())
    new_state = %State{state | value: new_value, vector_clock: new_vector_clock}
    reliable_broadcast(new_value, new_vector_clock, node(), new_nbMsg,  %State{wasDelivered: delivered} = state)
    {:noreply, new_state}
  end

  @impl true
  def handle_cast({:propose_value, new_value}, %State{value: _, vector_clock: vc, nbMsg: nbMsg} = state) do
    new_nbMsg = nbMsg + 1
    new_state = %State{state | value: new_value, nbMsg: new_nbMsg, vector_clock: DistributedCrypto.VectorClock.increment_entry(vc, node())}
    reliable_broadcast(new_value, vc, node(), new_nbMsg,  %State{wasDelivered: delivered} = state)
    {:noreply, new_state}
  end

  # causale broadcast
  @impl true
  def handle_cast({:update_value, node, msgSeq, new_value, incoming_vc}, %State{value: current_value, vector_clock: current_vc, message_queue: queue} = state) do
    reliable_broadcast(new_value, incoming_vc, node, msgSeq,  %State{wasDelivered: delivered} = state)
    cond do
      DistributedCrypto.VectorClock.vmax(incoming_vc, current_vc) -> #
        new_state = %State{
          state
          | value: new_value,
            vector_clock: incoming_vc,
            message_queue: [{incoming_vc, new_value} | queue]
        }
        {:noreply, process_causal_queue(new_state)}

      true ->
        new_state = %State{state | message_queue: [{incoming_vc, new_value} | queue]}
        {:noreply, new_state}
    end
  end

  ### Private Functions

  # broadcast fiable
  defp reliable_broadcast(value, vector_clock,node, msgSeq, %State{wasDelivered: delivered} = state) do
    current_node = node()

    if not MapSet.member?(delivered, {node, msgSeq}) do
      Node.list()
      |> Enum.each(fn member ->
        if member != current_node do
          GenServer.cast(
            {__MODULE__, member},
            {:update_value, node, msgSeq, value, vector_clock}
          )
        end
      end)
      updated_delivered = MapSet.put(delivered, {node, msgSeq})
      %State{state |  wasDelivered: updated_delivered}
    else
      state
    end
    new_vc = DistributedCrypto.VectorClock.increment_entry(vector_clock, node())
    %State{state |  vector_clock: new_vc}
  end

  defp process_causal_queue(%State{message_queue: []} = state), do: state

  defp process_causal_queue(%State{message_queue: [{vc, new_value} | tail], value: current_value, vector_clock: current_vc} = state) do
    if DistributedCrypto.VectorClock.vmax(vc, current_vc) do
      new_state = %State{
        state
        | value: new_value,
          vector_clock: vc,
          message_queue: tail
      }
      process_causal_queue(new_state)
    else
      state
    end
  end
end
