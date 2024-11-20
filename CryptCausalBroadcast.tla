---- MODULE DistributedCrypto ----
CONSTANT Nodes
CONSTANT Values
VARIABLE proc \* A function [Nodes -> State]
VARIABLE msgs \* A set of inflight messages
vars == <<proc, msgs>>

(* Define the types of messages *)
Msgs == UNION {
    [t : {"C_SEND"}, v : Values, dst : Nodes],
    [t : {"B_CAST"}, v : Values, dst : Nodes, src : Nodes]
}

(* Type invariant: proc holds values for all nodes, and msgs is a subset of valid message types *)
TypeOK ==
    /\ proc \in [Nodes -> Values]
    /\ msgs \subseteq Msgs

(* Broadcast message: send a B_CAST message *)
BCast(v, src, dst) == [t |-> "B_CAST", v |-> v, dst |-> dst, src |-> src]

(* Receive a C_SEND message and update the state of the node *)
RecvCSend(p) ==
    \E m \in msgs :
        /\ m.t = "C_SEND" /\ m.dst = p
        /\ proc' = [proc EXCEPT ![p] = m.v]
        /\ msgs' = (msgs \ {m}) \cup {BCast(m.v, p, n) : n \in Nodes}

(* Receive a B_CAST message and update the state of the node *)
RecvBCase(p) ==
    \E m \in msgs :
        /\ m.t = "B_CAST" /\ m.dst = p
        /\ proc' = [proc EXCEPT ![p] = m.v]
        /\ msgs' = msgs \ {m}

(* Initialization: All nodes start with the same value, and msgs is an empty set initially *)
Init ==
    \E v \in Values :
        /\ proc = [ p \in Nodes |-> v ]
        /\ msgs = {}

(* Next-state action: either handle a C_SEND or a B_CAST message for any node *)
Next ==
    \E p \in Nodes :
        \/ RecvCSend(p)
        \/ RecvBCase(p)

(* Fairness condition: eventually, some action (RecvCSend or RecvBCase) must happen *)
Fair == WF_vars(Next)

(* The full specification combining init, next-state, and fairness *)
Spec == Init /\ [][Next]_vars /\ Fair

(* InSync property: all nodes must eventually have the same value *)
InSync ==
    \E v \in Values :
        \A n \in Nodes : proc[n] = v

(* EventuallyInSync: all nodes eventually become synchronized *)
EventuallyInSync ==
    <>[] InSync

(* Theorem: The system maintains type consistency and eventually synchronizes *)
THEOREM (Spec => ([]TypeOK /\ EventuallyInSync))
PROOF OMITTED \* Checked by TLC.

THEOREM ASSUME Spec PROVE ([]TypeOK /\ EventuallyInSync)
PROOF OMITTED \* Checked by TLC.

====
