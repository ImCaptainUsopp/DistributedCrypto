---- MODULE CryptCausalBroadcast ----
(* Constances *)
CONSTANT Nodes
CONSTANT Values
VARIABLE proc 
VARIABLE msgs 
vars == <<proc, msgs>>

(* Les types de messages, noeud spécifique, broadcast *)
Msgs == UNION {
    [t : {"C_SEND"}, v : Values, dst : Nodes],
    [t : {"B_CAST"}, v : Values, dst : Nodes, src : Nodes]
}

(* Définis la valeur ok : proc à une valeur parmi value et le message est correct*)
TypeOK ==
    /\ proc \in [Nodes -> Values]
    /\ msgs \subseteq Msgs

(* Envoie d'un message broadcast *)
BCast(v, src, dst) == [t |-> "B_CAST", v |-> v, dst |-> dst, src |-> src]

(* Reçoit un message addressé à un noeud particulier et update la valeur *)
RecvCSend(p) ==
    \E m \in msgs :
        /\ m.t = "C_SEND" /\ m.dst = p
        /\ proc' = [proc EXCEPT ![p] = m.v]
        /\ msgs' = (msgs \ {m}) \cup {BCast(m.v, p, n) : n \in Nodes}

(* pareil mais broadcast *)
RecvBCase(p) ==
    \E m \in msgs :
        /\ m.t = "B_CAST" /\ m.dst = p
        /\ proc' = [proc EXCEPT ![p] = m.v]
        /\ msgs' = msgs \ {m}

(* Initialisation : chaque message commence avec la même valeur et pas de messages *)
Init ==
    \E v \in Values :
        /\ proc = [ p \in Nodes |-> v ]
        /\ msgs = {}

(*Prochaine etape : on envoie un message particulier ou on broadcast *)
Next ==
    \E p \in Nodes :
        \/ RecvCSend(p)
        \/ RecvBCase(p)

(* Les actions doivent avoir lieux *)
Fair == WF_vars(Next)
Spec == Init /\ [][Next]_vars /\ Fair

(* Conditions de synchronisation : les noeuds doivent avoir à un moment la même valeur (eventually) *)
InSync ==
    \E v \in Values :
        \A n \in Nodes : proc[n] = v

(* Il est garentit que chaque noeud aura la même valeur à un moment *)
EventuallyInSync ==
    <>[] InSync

(* Theorem: The system maintains type consistency and eventually synchronizes *)
THEOREM (Spec => ([]TypeOK /\ EventuallyInSync))
PROOF OMITTED \* Checked by TLC.

THEOREM ASSUME Spec PROVE ([]TypeOK /\ EventuallyInSync)
PROOF OMITTED \* Checked by TLC.

====
