defmodule DistributedCrypto.Node do
  use GenServer
  require Logger

  ### State Definition


  # valeur, vecteur clock, message queue , défault 0, init et [] --> chose de base quand tu crée un noeud
  defmodule State do
    @enforce_keys [:value, :vector_clock, :message_queue, :nbMsg, :wasDelivered,  :currentTerm, :votedFor, :currentRole, :currentLeader, :votesReceived, :log, :commitLength, :sentLength, :ackedLength, :message_buffer]
    defstruct value: 0, vector_clock: DistributedCrypto.VectorClock.new(), message_queue: [], nbMsg: 0, wasDelivered: MapSet.new(), currentTerm: 0, votedFor: nil, currentRole: :Follower, currentLeader: nil, votesReceived: MapSet.new(), log: [], commitLength: 0, sentLength: Map.new(), ackedLength: Map.new(), message_buffer: []
    @type t() :: %__MODULE__{value: integer(), vector_clock: DistributedCrypto.VectorClock.t(), message_queue: [{DistributedCrypto.VectorClock.t(), integer()}], nbMsg: integer(), wasDelivered: MapSet.t(),currentTerm: integer(),
    votedFor: Node.t(),
    currentRole: atom(),
    currentLeader: Node.t(),
    votesReceived: MapSet.t(),
    log: [{any(),any()}],
    commitLength: integer(),
    sentLength: %{optional(any()) => any()},
    ackedLength: %{optional(any()) => any()}}
  end

  #getters
  @spec get_state(node) :: State.t()
  def get_state(node) do
    GenServer.call({__MODULE__,node}, :get_state)
  end


  def get_current_term(%State{currentTerm: currentTerm}), do: currentTerm
  def get_voted_for(%State{votedFor: votedFor}), do: votedFor
  def get_current_role(%State{currentRole: currentRole}), do: currentRole
  def get_current_leader(%State{currentLeader: currentLeader}), do: currentLeader
  def get_votes_received(%State{votesReceived: votesReceived}), do: votesReceived
  def get_log(%State{log: log}), do: log
  def get_commit_length(%State{commitLength: commitLength}), do: commitLength
  def get_sent_length(%State{sentLength: sentLength}), do: sentLength
  def get_acked_length(%State{ackedLength: ackedLength}), do: ackedLength
  def get_message_buffer(%State{message_buffer: message_buffer}), do: message_buffer

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

  @spec launch_election_timeout(node()) :: any()
  def launch_election_timeout(node) do
    GenServer.cast({__MODULE__,node}, {:election_timeout})
  end




  ### Callbacks (appelés par l'utilisateur par les fonctions d'interface)

  # message intial
  @impl true
  def init(_) do
    Logger.info("#{node()} started and joined cluster.")
    {:ok, %State{value: 0, vector_clock: DistributedCrypto.VectorClock.new(), message_queue: [], nbMsg: 0, wasDelivered: MapSet.new(),currentTerm: 0, votedFor: nil, currentRole: :Follower, currentLeader: nil, votesReceived: MapSet.new(), log: [], commitLength: 0, sentLength: Map.new(), ackedLength: Map.new(), message_buffer: []}}
  end

  @impl true
  def handle_call(:get_value, _from, %State{value: value} = state) do # synchrone
    {:reply, value, state}
  end

  @impl true
  def handle_call(:get_state, _from, state) do
    {:reply, state, state}
  end

  @impl true
  def handle_cast(:increment, %State{value: value, vector_clock: vc, nbMsg: nbmsg} = state) do # asynchrone
    new_value = value + 1 # on incrément la valeur du noeud à l'intérieur
    new_nbMsg = nbmsg + 1
    new_vector_clock = DistributedCrypto.VectorClock.increment_entry(vc, node()) # on merge le vecteur interne et reçu
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
  def handle_cast({:update_value, new_value, incoming_vc}, %State{value: current_value, vector_clock: current_vc, message_queue: queue} = state) do
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

   ### RAFT Functions


  #Each node has a election timer, which is reset when receving the heartbeat from its leader.
  #When the Election Timer expires, the follower will transition to the role of candidate.
  #Following this transition, it will proceed to send voting requests to all nodes.
  @impl true
  def handle_cast({:election_timeout}, %State{currentTerm: currentTerm, currentRole: currentRole,log: log} = state) do
    Logger.info("Raft Voting timer down at #{node()}")
    %State{state | currentTerm: currentTerm + 1}
    if currentRole == :Leader do
      {:noreply, state}
    end
    %State{state | currentRole: :Candidate, votedFor: node(), votesReceived: MapSet.new([node()])}
    lastTerm = 0
    if length(log) > 0 do
      ^lastTerm = log[length(log)-1].term
    end
    Node.list()
      |> Enum.each(fn member ->
        if member != node() do
          GenServer.cast(
            {__MODULE__, member},
            {:voteRequest, node() , state.currentTerm , length(state.log), lastTerm}
          )
        end
      end)
      schedule_timeout(5000)
    {:ok,state}
  end

  #When node A receives a voting request from node B, it will perform the following steps:

  #Check if the term of B is greater than or equal the current term of A. If not, A will reject the voting request, since voting for B might result in multiple leaders in B’s term.
  #Check if the log of B is more or equal up-to-date than the log of A. If not, A will reject the voting request, since voting for B might result in log entries being lost.
  #Check if A has already voted for another candidate in the current term. If so, A will reject the voting request, since voting for B might result in multiple leaders in the current term.
  @impl true
  def handle_cast({:voteRequest, cNode , cTerm , cLogLength, cLogTerm}, %State{currentTerm: currentTerm,log: log, votedFor: votedFor} = state) do
    if cTerm > currentTerm do
      %State{state | currentTerm: cTerm, currentRole: :Follower, votedFor: nil}
    end
    lastTerm = 0
    if length(log) > 0 do
      ^lastTerm = log[length(log)-1].term
    end
    logOk = (cLogTerm > lastTerm) or (cLogTerm == lastTerm and cLogLength >= length(log))
    if cTerm == currentTerm and logOk and votedFor in {cNode , nil} do
      %State{state | votedFor: cNode}
      GenServer.call({__MODULE__, cNode},{:voteResponse, node(), currentTerm, true})
    else
      GenServer.call({__MODULE__, cNode},{:voteResponse, node(), currentTerm, false})
    end
    {:ok,state}
  end

  #Upon receiving voting responses, a node should check whether it has received a majority of votes.
  #If so, it should transition to the role of leader. Otherwise, it should remain a candidate.

  @impl true
  def handle_cast({:voteResponse,voterId, term, granted}, %State{currentTerm: currentTerm, currentRole: currentRole, votesReceived: votesReceived, log: log,sentLength: sentLength, ackedLength: ackedLength} = state) do
    if currentRole == :Candidate and term == currentTerm and granted do
      MapSet.put(votesReceived,voterId)
    end
    if MapSet.size(votesReceived) >= (length(Node.list()) + 1 + 1)/2 do
      %State{state | currentRole: Leader, currentLeader: node()}
      GenServer.call({__MODULE__, node()},{:leader_determined,state})
      Node.list()
      |> Enum.each(fn member ->
        if member != node() and member.currentRole == :Follower do
          Map.put(sentLength,member, length(log))
          Map.put(ackedLength,member,0)
          replicate_log(node(),member,state)
        end
      end)
    else
      if term > currentTerm do
        %State{state | currentTerm: term, currentRole: :Follower, votedFor: nil}
        schedule_timeout(5000)
      end
    end
    {:ok,state}
  end


  #When the application layer triggers a broadcast, the leader will append the broadcast message to its log, and send the log entry to all followers.
  #If the current node is not a leader, it will forward the broadcast message to the leader.

  def handle_cast({:raft_broadcast, msg: msg},%State{currentTerm: currentTerm, log: log, currentRole: currentRole, currentLeader: currentLeader, ackedLength: ackedLength, message_buffer: buffer} = state) do

    cond do
      currentRole == :Leader ->
        %State{state |  ackedLength: ackedLength, log: log ++ [%{msg: msg, term: currentTerm}]}
        Map.put(ackedLength,node(),length(log))
        Node.list()
        |> Enum.each(fn member ->
          if member != node() and member.currentRole == :Follower do
            replicate_log(node(),member,state)
          end
        end)
      currentLeader != nil ->
        GenServer.call({__MODULE__, currentLeader},:raft_broadcast, msg)
      true ->
        new_buffer = [msg | buffer]
       %State{state | message_buffer: new_buffer}
    end
    {:ok,state}
end


#When the replication timer expires, the leader will synchronize its log with all followers.
#The synchronization message also serves as a heartbeat message.
def handle_cast({:replication_timeout}, %State{currentRole: currentRole} = state) do
  if currentRole == :Leader do
    Node.list()
      |> Enum.each(fn member ->
        if member != node() and member.currentRole == :Follower do
          replicate_log(node(),member,state)
        end
      end)
  end
  {:ok,state}
end


#When a follower receives a synchronization message from the leader, it will perform the following steps:

 #   The follower will check whether the log is consistent with the log entries that the leader believes the follower has.
 #   If not, the follower will reject the synchronization request.

 #   If the log is consistent, the follower will append the suffix log entries to its own log.

 #   The follower will check whether the leader has committed any log entries. If so, the follower will commit the log entries that the leader has committed.

#To check whether the log is consistent, the follower will compare the term of the last log entry in the prefix with leader’s prefix_term.
#If they are not equal, the log is inconsistent.

def handle_cast({:logRequest,leaderId,term,prefixLen,prefixTerm, leaderCommit,suffix}, %State{currentTerm: currentTerm, log: log} = state) do
  if term > currentTerm do
    %State{state | currentTerm: term, votedFor: nil}
    schedule_timeout(5000)
  end
  if term == currentTerm do
    %State{state | currentRole: :Follower, currentLeader: :leaderId}
    GenServer.call({__MODULE__, node()},{:leader_determined,state})
  end
  logOk = (length(log) >= prefixLen) and (prefixLen == 0 or log[prefixLen-1].term == prefixTerm)
  if term == currentTerm and logOk do
    appendEntries(prefixLen , leaderCommit , suffix,state)
    ack = prefixLen + suffix.length
    GenServer.call({__MODULE__, leaderId},{:logResponse, node(),currentTerm,ack,true, state})
  else
    GenServer.call({__MODULE__, leaderId},{:logResponse, node(),currentTerm,0,false, state})
  end
  {:ok, state}
end

#When the leader receives a log response from a follower, it will perform the following steps:

#    If the synchronization is successful, the leader will update ackedLength and sentLength of the follower.

#    If the synchronization is failed, the leader will decrease sentLength of the follower by 1, and try again.

def handle_cast({:logResponse,follower,term,ack,success}, %State{currentTerm: currentTerm, currentRole: currentRole, sentLength: sentLength, ackedLength: ackedLength} = state) do
  if term == currentTerm and currentRole == :Leader do
    if success == true and ack >= ackedLength[follower] do
      Map.put(sentLength,follower,ack)
      Map.put(ackedLength,follower,ack)
      GenServer.call({__MODULE__, node()},[:commitLogEntries, state])
    else
      if term > currentTerm do
        %State{state | currentTerm: term, currentRole: :Follower, votedFor: nil}
        schedule_timeout(5000)
      end
    end
  end
end

#a function to deliver all the message in the buffer
def handle_cast(:leader_determined, %State{message_buffer: buffer, currentRole: :Leader} = state) do
  Enum.each(buffer, fn msg ->
    handle_cast({:raft_broadcast, msg}, state)
  end)
  {:noreply, %State{state | message_buffer: []}}
end

def handle_cast(:commitLogEntries, %State{commitLength: commitLength, log: log,currentTerm: currentTerm} = state) do
  nbNode = length(Node.list())
  minAcks = div(nbNode + 1,2)
  range = (commitLength + 1)..length(log)
  ready = Enum.filter(range, fn len -> acks(len,state) >= minAcks end)
  max_ready = Enum.max(ready, fn -> commitLength end)
  if (ready != {} and log[max_ready-1].term == currentTerm) do
    for i <- commitLength..(max_ready - 1) do
      log_entry = Enum.at(log, i - 1)
      # TODO deliver(log_entry.msg)
      IO.puts("msg delivered at node #{node()} : #{log_entry.msg} ")
    end
  end
  {:no_reply,state}
end




  ### Private Functions
  ### Private Functions


#  ReplicateLog is a helper function that synchronizes the log of the leader with a follower.
#  The simplest way to synchronize the log is to send the entire log to the follower. However, this is inefficient.
#  As mentioned earlier, the leader assumes that the log of the follower is the same as its own log when it becomes a leader.
#  Therefore, the leader only needs to send the log entries that the follower does not have.

#sentLength[follower] := log.length // the node assumes that the log of the follower is the same as its own log

#The leader maintains a variable sentLength for each follower. sentLength[follower] denotes the length of the log that the leader believes the follower has.
#When the leader synchronizes the logs with the follower, it will send the log entries after sentLength[follower].
#If the synchronization is failed, the leader will decrease sentLength[follower] by 1, and try again.

defp replicate_log(node,follower, %State{currentTerm: currentTerm,log: log, commitLength: commitLength, sentLength: sentLength} = state) do
  prefixLen = Map.get(sentLength,follower)
  suffix = Enum.slice(log, prefixLen..-1)
  prefixTerm = 0
  if prefixLen > 0 do
    ^prefixTerm = log[prefixLen-1].term
  end
  GenServer.call({__MODULE__, follower},{:logRequest,node,currentTerm,prefixLen,prefixTerm,commitLength,suffix,state})
end


#AppendEntries is a helper function that appends the suffix log entries to the log of the follower.

#Here we check whether the follower has the same suffix log entries as the leader.
#If not, the follower will remove all the log entries after prefix from its log, and append the suffix log entries from leader to its log.

defp appendEntries(prefixLen, leaderCommit, suffix, %State{log: log, commitLength: commitLength} = state) do
  if suffix.length > 0 and length(log)> prefixLen do
    index = min(length(log), prefixLen + suffix.length) - 1
    if log[index].term != suffix[index - prefixLen].term do
      %State{state | log: Enum.slice(log, 0..(prefixLen - 1))}
    end
  end
  if (prefixLen + suffix.length) > length(log) do
    start_index = length(log) - prefixLen
    end_index = length(suffix) - 1
    updated_log = Enum.reduce(start_index..end_index, log, fn i, acc_log -> acc_log ++ [Enum.at(suffix, i)] end)
    %State{state | log: updated_log}

  end
  if leaderCommit > commitLength do
    range = commitLength..(leaderCommit - 1)
    Enum.each(range, fn i ->
      ###TODO find how to deliver it, maybe update the state and send it back to broadcast it ???
      #deliver_to_application(Enum.at(log, i).msg)
      log_entry = Enum.at(log,i)
      IO.puts("msg delivered at app: #{log_entry.msg} ")
    end)
    %State{state | commitLength: leaderCommit}
    end
    {:no_reply,state}
end

#An helper function that count the number of node where the ackedLength is greater or equal than the argument
defp acks(x, %State{ackedLength: ackedLength}) do
  # Count the number of nodes whose ackedLength is greater than or equal to x
  ackedLength
  |> Enum.filter(fn {_node, acked} -> acked >= x end)
  |> length()
end



defp schedule_timeout(timeout) do
  Process.send_after(node(), :election_timeout, timeout)
end


  # broadcast fiable
  defp reliable_broadcast(value, vector_clock,node, msgSeq, %State{wasDelivered: delivered} = state) do
    current_node = node()

    if not MapSet.member?(delivered, {node, msgSeq}) do # delivré ????
      Node.list()   # non, on diffuse
      |> Enum.each(fn member ->
        if member != current_node do
          GenServer.cast(
            {__MODULE__, member},
            {:update_value, value, vector_clock}
          )
        end
      end)
      updated_delivered = MapSet.put(delivered, {node, msgSeq}) # on marche comme délivré
      %State{state |  wasDelivered: updated_delivered}
    else
      state
    end
    new_vc = DistributedCrypto.VectorClock.increment_entry(vector_clock, node()) # on update l'horloge vectorielle
    %State{state |  vector_clock: new_vc}
  end

  defp process_causal_queue(%State{message_queue: []} = state), do: state

  # vérifie si le message est compatible avec l'horloge actuelle, si il respect il est appliqué et on synchronise l'horloge vectorielle sinon on attend un message pour update
  defp process_causal_queue(%State{message_queue: [{vc, new_value} | tail], value: current_value, vector_clock: current_vc} = state) do # la queue
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
