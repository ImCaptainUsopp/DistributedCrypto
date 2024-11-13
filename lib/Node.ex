defmodule DistributedCrypto.Node do
  use GenServer
  require Logger

  ### State Definition

  defmodule State do
    @enforce_keys [:value,:vector_clock]
    defstruct value: 0 , vector_clock: VectorClock.fresh()
    @type t() :: %__MODULE__{value: integer(), vector_clock: VectorClock.t()}
  end

  ### Interface

  @spec start_link() :: :ignore | {:error, any} | {:ok, pid}
  def start_link() do
    GenServer.start_link(__MODULE__, {}, name: __MODULE__)
  end

  @spec propose_value(new_value :: integer()) :: :ok
  def propose_value(new_value) do
    GenServer.cast(__MODULE__, {:propose_value, new_value})
  end

  @spec propose_value(node(), new_value :: integer()) :: :ok
  def propose_value(node, new_value) do
    GenServer.cast({__MODULE__, node}, {:propose_value, new_value})
  end

  @spec increment() :: :ok
  def increment(), do: GenServer.cast(__MODULE__, :increment)

  @spec increment(node()) :: :ok
  def increment(node), do: GenServer.cast({__MODULE__, node}, :increment)

  @spec decrement() :: :ok
  def decrement(), do: GenServer.cast(__MODULE__, :decrement)

  @spec decrement(node()) :: :ok
  def decrement(node), do: GenServer.cast({__MODULE__, node}, :decrement)

  @spec get_value() :: integer()
  def get_value() do
    GenServer.call(__MODULE__, :get_value)
  end

  @spec get_value(node()) :: integer()
  def get_value(node) do
    GenServer.call({__MODULE__, node}, :get_value)
  end

  @spec ping(node()) :: :pong | :pang
  def ping(node), do: :pong

  ### Callbacks

  @impl true
  def init(_) do
    Logger.info("#{node()} started and joined cluster.")
    {:ok, %State{value: 0, vector_clock: VectorClock.fresh()}}

  end

  @impl true
  def handle_call(:get_value, _from, %State{value: value} = state) do
    {:reply, value, state}
  end

  # take the max btw the received vector_clock and the node one

  @impl true
  def handle_cast(:increment, %State{value: value, vector_clock: vc} = state) do
    new_value = value + 1
    new_state = %State{state | value: new_value, vector_clock: VectorClock.increment(vc, node())}
    broadcast_value_update(new_value,vc)
    {:noreply, new_state}
  end

  @impl true
  def handle_cast(:decrement, %State{value: value, vector_clock: vc} = state) do
    new_value = value - 1
    new_state = %State{state | value: new_value, vector_clock: VectorClock.increment(vc, node())}
    broadcast_value_update(new_value,vc)
    {:noreply, new_state}
  end

  @impl true
  def handle_cast({:propose_value, new_value}, %State{value: _, vector_clock: vc} = state) do
    new_state = %State{state | value: new_value, vector_clock: VectorClock.increment(vc, node())}
    broadcast_value_update(new_value,vc)
    {:noreply, new_state}
  end
  @impl true
  def handle_cast({:update_value, new_value, []}, %State{value: _, vector_clock: _} = state) do
    new_state = %State{state | value: new_value, vector_clock: VectorClock.fresh()}
    {:noreply, new_state}
  end

  @impl true
  def handle_cast({:update_value, new_value, incoming_vc}, %State{value: current_value, vector_clock: current_vc} = state) do
    if VectorClock.dominates(incoming_vc, current_vc) do
      new_state = %State{state | value: new_value, vector_clock: incoming_vc}
      {:noreply, new_state}
    else
      {:noreply, state}
    end
  end


  ### Private Functions

  defp broadcast_value_update(new_value,vector_clock) do
    members = Node.list()
    Enum.each(members, fn node -> GenServer.cast({__MODULE__, node}, {:update_value, new_value,vector_clock}) end)
  end
end
