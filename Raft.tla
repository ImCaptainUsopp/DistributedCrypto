------------------- MODULE Raft -------------------

EXTENDS Naturals, Sequences, TLC

(* Configuration initiale *)
CONSTANTS N \* Nombre de serveurs

(* Etats possibles des serveurs *)
CONSTANT Roles \in {"Follower", "Candidate", "Leader"}

VARIABLES 
    role,         \* Role de chaque serveur (tableau de taille N)
    term,         \* Terme actuel pour chaque serveur (tableau de taille N)
    votes,        \* Votes re�us par chaque serveur (tableau de taille N)
    log,          \* Journaux de chaque serveur (tableau de s�quences)
    commitIndex   \* Indice d'engagement des journaux par serveur

(* Init : tout le monde est follower, term initialis� � zero, aucune vote re�u, pas de log et l'index du commit � zero *)
Init == 
    /\ role = [i \in 1..N |-> "Follower"]
    /\ term = [i \in 1..N |-> 0]
    /\ votes = [i \in 1..N |-> {}]
    /\ log = [i \in 1..N |-> <<>>]
    /\ commitIndex = [i \in 1..N |-> 0]

(* Changement de role d'un serveur *)
ChangeRole(server, newRole) ==
    role' = [role EXCEPT ![server] = newRole]

(* Nouvelle election : le serveur increment son terme, vote pour lui m�me et change son r�le *)
StartElection(server) ==
    /\ term' = [term EXCEPT ![server] = term[server] + 1] \* Incr�mente le terme
    /\ votes' = [votes EXCEPT ![server] = {server}]        \* Vote pour soi-m�mme
    /\ ChangeRole(server, "Candidate")

(* R�ception d'un vote, on regarde si le valeur est valide, si le serveur qui re�oit est bien candidat puis update de la liste *)
ReceiveVote(server, voter) ==
    /\ voter \in 1..N
    /\ role[server] = "Candidate"
    /\ votes' = [votes EXCEPT ![server] = votes[server] \union {voter}]

(*Si N/2 notes alors on change le role pour leader *)
ElectLeader(server) ==
    /\ Cardinality(votes[server]) > N / 2
    /\ ChangeRole(server, "Leader")

(* Ajout d'une nouvelle entr�e au journal d'un leader : donc ajouter une nouvelle op�ration *)
AppendLogEntry(server, entry) ==
    /\ role[server] = "Leader"
    /\ log' = [log EXCEPT ![server] = Append(log[server], entry)]

(* R�plication d'une entr�e sur un suiveur : synchronise suiveur et leader *)
ReplicateLogEntry(leader, follower) ==
    /\ role[leader] = "Leader"
    /\ role[follower] = "Follower"
    /\ log' = [log EXCEPT ![follower] = log[leader]]

(*Indique que le le serveur a valid� les entr�es jusqu'� un certain points*)
UpdateCommitIndex(server, index) ==
    /\ commitIndex' = [commitIndex EXCEPT ![server] = index]

(* Propri�t�s de s�curit� : garentit qu'il n'y aura pas de chose en dehors de la proc�dure *)
ElectionSafety == \* seulement un leader
    \A term \in DOMAIN term : \A server1, server2 \in 1..N :
        (role[server1] = "Leader" /\ role[server2] = "Leader" /\ term[server1] = term[server2]) => server1 = server2

StateMachineSafety == \* coh�rence des journeaux, les journeaux de 2 tabs sont �gaux
    \A i \in DOMAIN log : \A server1, server2 \in 1..N :
        commitIndex[server1] >= i /\ commitIndex[server2] >= i => log[server1][i] = log[server2][i]

(* Propri�t� de vivacit� : tout peut se passer *)
LeaderLiveness ==
    \E server \in 1..N : role[server] = "Leader" \* au moins un leader 

LogLiveness ==
    \E server \in 1..N : commitIndex[server] > 0 \* au moins un index >0

(* Etapes de transition *)
Next == 
    \/ \E server \in 1..N : StartElection(server) \* un serveur commence un �lection
    \/ \E server, voter \in 1..N : ReceiveVote(server, voter) \* un serveur peut voter pour un autre
    \/ \E server \in 1..N : ElectLeader(server) \* un serveur puet �tre �lu leadrr
    \/ \E server \in 1..N, entry \in Nat : AppendLogEntry(server, entry) \* un leader peut ajouter une entr�e � son journal
    \/ \E leader, follower \in 1..N : ReplicateLogEntry(leader, follower) \* un leader peut r�pliquer sur un suiveur
    \/ \E server \in 1..N, index \in Nat : UpdateCommitIndex(server, index) \* on peut mettre � jour l'indice de validation     

(* Sp�cification du mod�le : on init puis on suit nex*)
Spec == Init /\ [][Next]_<<role, term, votes, log, commitIndex>>

(* Propri�t�s � v�rifier *)
Invariant == ElectionSafety /\ StateMachineSafety
Liveness == LeaderLiveness /\ LogLiveness

===================================================
