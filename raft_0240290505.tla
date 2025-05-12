
--------------------------- MODULE raft_0240290505 ---------------------------

\* --------------------------- raftConstants ---------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* The set of client requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader, Switch

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse

\* for instrumentation to limit model state space
CONSTANTS MaxClientRequests

\* Maximum times a server can become a leader
CONSTANTS MaxBecomeLeader

\* Maximum term number allowed in the model
CONSTANTS MaxTerm


\* --------------------------- raftVariables ---------------------------

\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another. This is a function mapping Message to Nat.
VARIABLE messages

\* Counter for how many times each server has become leader
VARIABLE leaderCount

\* maximum client requests so far
VARIABLE maxc

\* variable for tracking entry commit message counts
\* Maps <<logIndex, logTerm>> to a record tracking message counts.
\* [ sentCount |-> Nat,   \* AppendEntriesRequests sent for this entry
\*   ackCount  |-> Nat,   \* Successful AppendEntriesResponses received for this entry
\*   committed |-> Bool ] \* Flag indicating if the entry is committed
VARIABLE entryCommitStats

\* 
VARIABLE Servers

\* index into Server
VARIABLE switchIndex

\* Temporary storage for requests received by the switch before they're ordered
\* Maps request value to the full payload entry
VARIABLE switchBuffer

\* Each server's buffer of unordered requests received from the switch
\* Maps from Server to a set of request values pending ordering
VARIABLE unorderedRequests

\* Records which <<value, term>> pairs the current switch has sent to each server.
\* Maps Server ID -> Set of <<Value, Term>> pairs.
VARIABLE switchSentRecord

\* New HovercRaft variables
hovercraftVars == <<switchBuffer, unorderedRequests, switchIndex, switchSentRecord>>

instrumentationVars == <<leaderCount, maxc, entryCommitStats>>

\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor
serverVars == <<currentTerm, state, votedFor>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex
logVars == <<log, commitIndex>>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE votesResponded
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted
\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Function from each server that voted for this candidate in its currentTerm
\* to that voter's log.
VARIABLE voterLog
candidateVars == <<votesResponded, votesGranted, voterLog>>

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex
leaderVars == <<nextIndex, matchIndex>>

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars, Servers>>


\* --------------------------- raftHelpers ---------------------------

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Servers) : Cardinality(i) * 2 > Cardinality(Servers)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        msgs
       \* [msgs EXCEPT ![m] = IF msgs[m] < 2 THEN msgs[m] + 1 ELSE 2 ]
    ELSE
        msgs @@ (m :> 1)

WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = IF msgs[m] > 0 THEN msgs[m] - 1 ELSE 0 ]
    ELSE
        msgs

\* Add a message to the bag of messages.
Send(m) == messages' = WithMessage(m, messages)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) == messages' = WithoutMessage(m, messages)

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* Combination of Send and Discard
Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

min(a, b) == IF a < b THEN a ELSE b

ValidMessage(msgs) ==
    { m \in DOMAIN messages : msgs[m] > 0 }

\* The prefix of the log of server i that has been committed up to term x
CommittedTermPrefix(i, x) ==
    \* Only if log of i is non-empty, and if there exists an entry up to the term x
    IF Len(log[i]) /= 0 /\ \E y \in DOMAIN log[i] : log[i][y].term <= x
    THEN
      \* then, we use the subsequence up to the maximum committed term of the leader
      LET maxTermIndex ==
          CHOOSE y \in DOMAIN log[i] :
            /\ log[i][y].term <= x
            /\ \A z \in DOMAIN log[i] : log[i][z].term <= x  => y >= z
      IN SubSeq(log[i], 1, min(maxTermIndex, commitIndex[i]))
    \* Otherwise the prefix is the empty tuple
    ELSE << >>

CheckIsPrefix(seq1, seq2) ==
    /\ Len(seq1) <= Len(seq2)
    /\ \A i \in 1..Len(seq1) : seq1[i] = seq2[i]

\* The prefix of the log of server i that has been committed
Committed(i) ==
    IF commitIndex[i] = 0
    THEN << >>
    ELSE SubSeq(log[i],1,commitIndex[i])

MyConstraint == (\A i \in Servers: currentTerm[i] <= MaxTerm /\ Len(log[i]) <= MaxClientRequests ) 
                /\ (\A m \in DOMAIN messages: messages[m] <= 1)

Symmetry == Permutations(Servers)


\* --------------------------- raftInit ---------------------------

InitHistoryVars == voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]
Init == /\ messages = [m \in {} |-> 0]
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ maxc = 0
        /\ leaderCount = [i \in Server |-> 0]
        /\ entryCommitStats = [ idx_term \in {} |-> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ] ] \* Initialize new variable

\* MyInit remains unchanged for the core Raft state, entryCommitStats is handled in Init.
MyInit ==
    LET ServerIds == CHOOSE ids \in [1..3 -> Server] : TRUE
        r1 == ServerIds[1]
        r2 == ServerIds[2]
        r3 == ServerIds[3]
    IN
    /\ commitIndex = [s \in Server |-> 0]
    /\ currentTerm = [s \in Server |-> 2]
    /\ leaderCount = [s \in Server |-> IF s = r2 THEN 1 ELSE 0]
    /\ log = [s \in Server |-> <<>>]
    /\ matchIndex = [s \in Server |-> [t \in Server |-> 0]]
    /\ maxc = 0
    /\ messages = [m \in {} |-> 0]  \* Start with empty messages
    /\ nextIndex = [s \in Server |-> [t \in Server |-> 1]]
    /\ state = [s \in Server |-> IF s = r2 THEN Leader ELSE Follower]
    /\ votedFor = [s \in Server |-> IF s = r2 THEN Nil ELSE r2]
    /\ voterLog = [s \in Server |-> IF s = r2 THEN (r1 :> <<>> @@ r3 :> <<>>) ELSE <<>>]
    /\ votesGranted = [s \in Server |-> IF s = r2 THEN {r1, r3} ELSE {}]
    /\ votesResponded = [s \in Server |-> IF s = r2 THEN {r1, r3} ELSE {}]
    /\ entryCommitStats = [ idx_term \in {} |-> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ] ] \* Initialize here too


MyNewInit ==
    LET ServerSet4 == CHOOSE S \in SUBSET(Server) : Cardinality(S) = 4
        TheSwitchId == CHOOSE s \in ServerSet4 : TRUE
        ServersSet == ServerSet4 \ {TheSwitchId}
        ServerIds == CHOOSE ids \in [1..3 -> ServersSet] : TRUE
        r1 == TheSwitchId
        r2 == ServerIds[1]
        r3 == ServerIds[2]
        r4 == ServerIds[3]
    IN
    \* /\ PrintT("MyInit: switchId=" \o ToString(TheSwitchId))
    \* /\ PrintT("MyInit: ServersSet=" \o ToString(ServerSet4))
    \* /\ PrintT("MyInit: Servers=" \o ToString(Servers))
    \* /\ PrintT("MyInit: Servers111=" \o ToString(ServerSeq))
    /\ Servers = ServersSet
    /\ commitIndex = [s \in Server |-> 0]
    /\ currentTerm = [s \in Server |-> 2]
    /\ leaderCount = [s \in Server |-> IF s = r2 THEN 1 ELSE 0]
    /\ log = [s \in Server |-> <<>>]
    /\ matchIndex = [s \in Server |-> [t \in Server |-> 0]]
    /\ maxc = 0
    /\ messages = [m \in {} |-> 0]  \* Start with empty messages
    /\ nextIndex = [s \in Server |-> [t \in Server |-> 1]]
    /\ state = [s \in Server |-> IF s = r2 THEN Leader ELSE IF s = TheSwitchId THEN Switch ELSE Follower]
    /\ switchBuffer = [v \in {} |-> [term |-> 0, value |-> "", payload |-> ""]]
    /\ switchIndex = TheSwitchId
    /\ switchSentRecord = [s \in Server |-> {}]
    /\ unorderedRequests = [s \in Server |-> {}]
    /\ votedFor = [s \in Server |-> IF s = r2 THEN Nil ELSE r2]
    /\ voterLog = [s \in Server |-> IF s = r2 THEN (r1 :> <<>> @@ r3 :> <<>> @@ r4 :> <<>>) ELSE <<>>]
    /\ votesGranted = [s \in Server |-> IF s = r2 THEN {r1, r3, r4} ELSE {}]
    /\ votesResponded = [s \in Server |-> IF s = r2 THEN {r1, r3, r4} ELSE {}]
    /\ entryCommitStats = [ idx_term \in {} |-> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ] ]


\* --------------------------- raftActionsSolution ---------------------------

----
\* Define state transitions

\* Modified to allow Restarts only for Leaders
\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
\* Also persists messages and instrumentation vars elections, maxc, leaderCount, entryCommitStats
Restart(i) ==
    /\ state[i] = Leader \* limit restart to leaders todo mc
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, instrumentationVars>>

\* Modified to restrict Timeout to just Followers
\* Server i times out and starts a new election. Follower -> Candidate
Timeout(i) == /\ state[i] \in {Follower} \*, Candidate
              /\ currentTerm[i] < MaxTerm
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              /\ UNCHANGED <<messages, leaderVars, logVars, instrumentationVars>>

\* Modified to restrict Leader transitions, bounded by MaxBecomeLeader
\* Candidate i transitions to leader. Candidate -> Leader
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ leaderCount[i] < MaxBecomeLeader
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ leaderCount' = [leaderCount EXCEPT ![i] = leaderCount[i] + 1]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars, maxc, entryCommitStats>>

\* Modified up to MaxTerm; Back To Follower
\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ m.mterm < MaxTerm
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, instrumentationVars>>

\***************************** REQUEST VOTE **********************************************
\* Message handlers
\* i = recipient, j = sender, m = message

\* Candidate i sends j a RequestVote request.
RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \notin votesResponded[i]
    /\ Send([mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars>>

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 \* mlog is used just for the `elections' history variable for
                 \* the proof. It would not exist in a real implementation.
                 mlog         |-> log[i],
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, instrumentationVars>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] =
                              voterLog[i] @@ (j :> m.mlog)]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted, voterLog>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, instrumentationVars>>

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars>>

\***************************** AppendEntries **********************************************

\* Modified. Leader i receives a client request to add v to the log. up to MaxClientRequests.
ClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ maxc < MaxClientRequests 
    /\ LET entryTerm == currentTerm[i]
           entry == [term |-> entryTerm, value |-> v]
           entryExists == \E j \in DOMAIN log[i] : log[i][j].value = v /\ log[i][j].term = entryTerm
           newLog == IF entryExists THEN log[i] ELSE Append(log[i], entry)
           newEntryIndex == Len(log[i]) + 1
           newEntryKey == <<newEntryIndex, entryTerm>>
       IN
        /\ log' = [log EXCEPT ![i] = newLog]
        /\ maxc' = IF entryExists THEN maxc ELSE maxc + 1
        /\ entryCommitStats' =
              IF ~entryExists /\ newEntryIndex > 0 \* Only add stats for truly new entries
              THEN entryCommitStats @@ (newEntryKey :> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ])
              ELSE entryCommitStats
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex, leaderCount>>

\* i: leader, v: value
SwitchClientRequest(switchIdx, i, v) == 
    \* /\ i /= switchIdx
    /\ maxc < MaxClientRequests
    \* /\ state[switchIdx] = Switch
    /\ LET entryTerm == currentTerm[i]
           newEntry == [term |-> entryTerm, value |-> v, payload |-> v]
           entryExists == v \in DOMAIN switchBuffer
       IN
        /\ switchBuffer' = IF entryExists
                           THEN switchBuffer
                           ELSE switchBuffer @@ (v :> newEntry) \* Add/override v with newEntry
        /\ maxc' = IF entryExists THEN maxc ELSE maxc + 1

    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, leaderCount, entryCommitStats, unorderedRequests, switchIndex, switchSentRecord, Servers>>

SwitchClientRequestReplicate(switchIdx, i, v) == 
    \* /\ i /= switchIdx
    /\ LET entryToReplicate == switchBuffer[v]
           valueTermPair == <<entryToReplicate.value, entryToReplicate.term>>
       IN
          /\ valueTermPair \notin switchSentRecord[i]
          /\ unorderedRequests' = [unorderedRequests EXCEPT ![i] = @ \cup {v}] \* we only store value, we can use that as an index to the switch buffer to get the full entry
          /\ switchSentRecord' = [switchSentRecord EXCEPT ![i] = @ \cup {valueTermPair}]

    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, leaderCount, entryCommitStats, maxc, switchBuffer, switchIndex, Servers>>

\* Action: Leader 'i' add entry corresponding to value v it to its own log.
LeaderIngestHovercRaftRequest(i, v) ==
    /\ v \in unorderedRequests[i]
    /\ LET
          newLogEntry == switchBuffer[v]
          newLeaderLog == Append(log[i], newLogEntry)
          newEntryIndex == Len(log[i]) + 1
          newEntryKey == <<newEntryIndex, newLogEntry.term>>
          valueAlreadyInLog == \E idx \in DOMAIN log[i] : log[i][idx].value = newLogEntry.value \* also check payload and term fields?

       IN
        /\ ~valueAlreadyInLog
        /\ log' = [log EXCEPT ![i] = newLeaderLog]
        /\ entryCommitStats' = entryCommitStats @@ (newEntryKey :> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ])
        /\ unorderedRequests' = [unorderedRequests EXCEPT ![i] = @ \ {v}]

    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex, leaderCount, maxc, switchBuffer, switchIndex, switchSentRecord, Servers>>

\* Modified. Leader i sends j an AppendEntries request containing exactly 1 entry. It was up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ Len(log[i]) > 0  \* Only proceed if the leader has entries to send
    /\ nextIndex[i][j] <= Len(log[i])  \*  Only proceed if there are entries to send to this follower
    /\ matchIndex[i][j] < nextIndex[i][j] \* Only send if follower hasn't already acknowledged this index
    /\ LET entryIndex == nextIndex[i][j]
           entry == log[i][entryIndex]
           entryMetaData == [term |-> entry.term, value |-> entry.value] \*new
           entries == << entryMetaData >>
           entryKey == <<entryIndex, entry.term>>
           prevLogIndex == entryIndex - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           \* lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           \* entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
           
       IN Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,
                \* mlog is used as a history variable for the proof.
                \* It would not exist in a real implementation.
                mlog           |-> log[i],
                mcommitIndex   |-> Min({commitIndex[i], entryIndex}), \* lastEntry}),
                msource        |-> i,
                mdest          |-> j])
       /\ entryCommitStats' =
            IF entryKey \in DOMAIN entryCommitStats /\ ~entryCommitStats[entryKey].committed
            THEN [entryCommitStats EXCEPT ![entryKey].sentCount = @ + 1]
            ELSE entryCommitStats         
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, maxc, leaderCount, hovercraftVars, Servers>>

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
        \* an entry is not found in server i's cache for the metadata received from j
        \* this can be referred to as an hovercRaft mismatch condition
        cacheMissHovercRaft ==
          /\ m.mentries /= <<>>
          /\ LET entry == m.mentries[1]
                 v == entry.value
                 msgTerm == entry.term
             IN 
             \lnot ( /\ v \in unorderedRequests[i]
                     /\ v \in DOMAIN switchBuffer
                     /\ switchBuffer[v].term = msgTerm )

    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* reject request
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \lnot logOk
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ cacheMissHovercRaft
             /\ Reply([mtype           |-> AppendEntriesResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mmatchIndex     |-> 0,
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ UNCHANGED <<serverVars, logVars, unorderedRequests>>
          \/ \* return to follower state
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages, unorderedRequests>>
          \/ \* accept request
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                IN \/ \* already done with request
                       /\ \/ m.mentries = << >>
                          \/ /\ m.mentries /= << >>
                             /\ Len(log[i]) >= index
                             /\ log[i][index].term = m.mentries[1].term
                          \* This could make our commitIndex decrease (for
                          \* example if we process an old, duplicated request),
                          \* but that doesn't really affect anything.
                       /\ commitIndex' = [commitIndex EXCEPT ![i] =
                                              m.mcommitIndex]   
\*                       /\ commitIndex' = [commitIndex EXCEPT ![i] = 
\*                                            IF commitIndex[i] < m.mcommitIndex THEN 
\*                                                Min({m.mcommitIndex, Len(log[i])}) 
\*                                            ELSE 
\*                                                commitIndex[i]]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex +
                                                     Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, log, unorderedRequests>>
                   \/ \* conflict: remove 1 entry (simplified from original spec - assumes entry length 1)
                      \* since we do not send empty entries, we have to provide a larger set of values to ensure some progress
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) >= index
                       /\ log[i][index].term /= m.mentries[1].term
                       /\ LET newLog == SubSeq(log[i], 1, index - 1) \* Truncate log
                          IN log' = [log EXCEPT ![i] = newLog]
\*                       /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |->
\*                                          log[i][index2]]
\*                          IN log' = [log EXCEPT ![i] = new]
                       /\ UNCHANGED <<serverVars, commitIndex, messages, unorderedRequests>>
                   \/ \* no conflict: append entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) = m.mprevLogIndex
                       /\ \lnot cacheMissHovercRaft
                       /\ LET
                            entryMetaData == m.mentries[1]
                            fullEntry == switchBuffer[entryMetaData.value]
                            entryForLocalLog == [term |-> entryMetaData.term,
                                                  value |-> entryMetaData.value,
                                                  payload |-> fullEntry.payload]
                          IN 
                             /\ log' = [log EXCEPT ![i] = Append(log[i],entryForLocalLog)]
                             /\ unorderedRequests' = [unorderedRequests EXCEPT ![i] = @ \ {entryMetaData.value}] \* remove since it is now ordered


                       /\ UNCHANGED <<serverVars, commitIndex, messages>>
       /\ UNCHANGED <<candidateVars, leaderVars, instrumentationVars, switchIndex, switchBuffer, switchSentRecord, Servers>> \* entryCommitStats unchanged on followers

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ LET \*newMatchIndex == IF matchIndex[i][j] > m.mmatchIndex THEN matchIndex[i][j] ELSE m.mmatchIndex
                 newMatchIndex == m.mmatchIndex
                 entryKey == IF newMatchIndex > 0 /\ newMatchIndex <= Len(log[i])
                              THEN <<newMatchIndex, log[i][newMatchIndex].term>>
                              ELSE <<0, 0>> \* Invalid index or empty log
             IN \*/\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = newMatchIndex + 1]
                /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
                /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
                \*/\ matchIndex' = [matchIndex EXCEPT ![i][j] = newMatchIndex]
                /\ entryCommitStats' =
                     IF /\ entryKey /= <<0, 0>>
                        /\ entryKey \in DOMAIN entryCommitStats
                        /\ ~entryCommitStats[entryKey].committed
                     THEN [entryCommitStats EXCEPT ![entryKey].ackCount = @ + 1]
                     ELSE entryCommitStats                     
       \/ /\ \lnot m.msuccess \* not successful
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                               Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex, entryCommitStats>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, maxc, leaderCount, hovercraftVars, Servers>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Servers :
                                         matchIndex[i][k] >= index}
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
           committedIndexes == { k \in Nat : /\ k > commitIndex[i]
                                             /\ k <= newCommitIndex }
           \* Identify the keys in entryCommitStats corresponding to newly committed entries
           keysToUpdate == { key \in DOMAIN entryCommitStats : key[1] \in committedIndexes }           
       IN /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
          \* Update the 'committed' flag for the relevant entries in entryCommitStats
          /\ entryCommitStats' =
               [ key \in DOMAIN entryCommitStats |->
                   IF key \in keysToUpdate
                   THEN [ entryCommitStats[key] EXCEPT !.committed = TRUE ] \* Update record
                   ELSE entryCommitStats[key] ]                             \* Keep old record       
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, maxc, leaderCount, hovercraftVars, Servers>>

\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars>>

\* --------------------------- raftSpec ---------------------------

\* This is the formal specification for the Raft consensus algorithm.
\* Modified by Ovidiu Marcu. Simplified model and performance invariants added.
\* Modified further to track message counts for entry commitment.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

\* Receive a message.
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
       \/ UpdateTerm(i, j, m)
       \/ /\ m.mtype = RequestVoteRequest
          /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestVoteResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestVoteResponse(i, j, m)
       \/ /\ m.mtype = AppendEntriesRequest
          /\ HandleAppendEntriesRequest(i, j, m)
       \/ /\ m.mtype = AppendEntriesResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleAppendEntriesResponse(i, j, m)

\* Defines how the variables may transition.
Next == 
           \/ \E i \in Server : Timeout(i)
\*           \/ \E i \in Server : Restart(i)
           \/ \E i,j \in Server : i /= j /\ RequestVote(i, j)
           \/ \E i \in Server : BecomeLeader(i)
           \/ \E i \in Server, v \in Value : state[i] = Leader /\ ClientRequest(i, v)
           \/ \E i \in Server : AdvanceCommitIndex(i)
           \/ \E i,j \in Server : i /= j /\ AppendEntries(i, j)
           \/ \E m \in {msg \in ValidMessage(messages) : \* to visualize possible messages
                    msg.mtype \in {RequestVoteRequest, RequestVoteResponse, AppendEntriesRequest, AppendEntriesResponse}} : Receive(m)
\*           \/ \E m \in {msg \in ValidMessage(messages) : 
\*                    msg.mtype \in {AppendEntriesRequest}} : DuplicateMessage(m)
\*           \/ \E m \in {msg \in ValidMessage(messages) : 
\*                    msg.mtype \in {RequestVoteRequest}} : DropMessage(m)

MyNext == 
\*           \/ \E i \in Server : Timeout(i)
\*           \/ \E i \in Server : Restart(i)
\*           \/ \E i,j \in Server : i /= j /\ RequestVote(i, j)
\*           \/ \E i \in Server : BecomeLeader(i)
           \/ \E i \in Server, v \in Value : state[i] = Leader /\ ClientRequest(i, v)
           \/ \E i \in Server : AdvanceCommitIndex(i)
           \/ \E i,j \in Server : i /= j /\ AppendEntries(i, j)
           \/ \E m \in {msg \in ValidMessage(messages) : \* to visualize possible messages
                    msg.mtype \in {AppendEntriesRequest, AppendEntriesResponse}} : Receive(m)
\*           \/ \E m \in {msg \in ValidMessage(messages) : 
\*                    msg.mtype \in {AppendEntriesRequest}} : DuplicateMessage(m)
\*           \/ \E m \in {msg \in ValidMessage(messages) : 
\*                    msg.mtype \in {RequestVoteRequest}} : DropMessage(m)

MySwitchNext == 
  \/ \E i \in Servers, v \in Value : state[i] = Leader /\ SwitchClientRequest(switchIndex, i, v)
  \/ \E i \in Servers, v \in DOMAIN switchBuffer : SwitchClientRequestReplicate(switchIndex, i, v)
  \/ \E i \in Servers, v \in DOMAIN switchBuffer : state[i] = Leader /\ LeaderIngestHovercRaftRequest(i, v)
  \/ \E i \in Servers : AdvanceCommitIndex(i)
  \/ \E i,j \in Servers : i /= j /\ AppendEntries(i, j)
  \/ \E m \in {msg \in ValidMessage(messages) : msg.mtype \in {AppendEntriesRequest, AppendEntriesResponse}} : Receive(m)


\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

MySpec == MyNewInit /\ [][MySwitchNext]_vars
\* MySpec == MyInit /\ [][MyNext]_vars

\* -------------------- Invariants --------------------

MoreThanOneLeaderInv ==
    \A i,j \in Servers :
        (/\ currentTerm[i] = currentTerm[j]
         /\ state[i] = Leader
         /\ state[j] = Leader)
        => i = j

\* fake invariant to check the first two actions in MySwitchNext
AllServersHaveOneUnorderedRequestInv ==
    \E s \in Servers :  Cardinality(unorderedRequests[s]) /= 2

\* Every (index, term) pair determines a log prefix.
\* From page 8 of the Raft paper: "If two logs contain an entry with the same index and term, then the logs are identical in all preceding entries."
LogMatchingInv ==
    \A i, j \in Servers : i /= j =>
        \A n \in 1..min(Len(log[i]), Len(log[j])) :
            log[i][n].term = log[j][n].term =>
            SubSeq(log[i],1,n) = SubSeq(log[j],1,n)

\* The committed entries in every log are a prefix of the
\* leader's log up to the leader's term (since a next Leader may already be
\* elected without the old leader stepping down yet)
LeaderCompletenessInv ==
    \A i \in Servers :
        state[i] = Leader =>
        \A j \in Server : i /= j =>
            CheckIsPrefix(CommittedTermPrefix(j, currentTerm[i]),log[i])
            
    
\* Committed log entries should never conflict between servers
LogInv ==
    \A i, j \in Servers :
        \/ CheckIsPrefix(Committed(i),Committed(j)) 
        \/ CheckIsPrefix(Committed(j),Committed(i))

\* Note that LogInv checks for safety violations across space
\* This is a key safety invariant and should always be checked
THEOREM Spec => ([]LogInv /\ []LeaderCompletenessInv /\ []LogMatchingInv /\ []MoreThanOneLeaderInv) 

\* --------------------------- raftModelPerf ---------------------------

\*instrumentation and performance invariants

\* A leader's maxc should remain under MaxClientRequests
MaxCInv == (\E i \in Server : state[i] = Leader) => maxc <= MaxClientRequests

\* No server can become leader more than MaxBecomeLeader times
LeaderCountInv == \E i \in Server : (state[i] = Leader => leaderCount[i] <= MaxBecomeLeader)

\* No server can have a term exceeding MaxTerm
MaxTermInv == \A i \in Server : currentTerm[i] <= MaxTerm

\* Check lower bound for message counts on committed entries ----
\* For any entry that has been marked as committed, verify that either the number
\* of AppendEntries requests sent OR the number of successful acknowledgments received
\* is at least the minimum number of followers required to form a majority.
\* will fail when an entry was sent twice to a follower and no response was acked yet, which is normal
EntryCommitMessageCountInv ==
    LET NumFollowers == Cardinality(Server) - 1
        MinFollowersForMajority == Cardinality(Server) \div 2
    IN \A key \in DOMAIN entryCommitStats :
        LET stats == entryCommitStats[key]
        IN IF stats.committed
           THEN (stats.sentCount >= MinFollowersForMajority /\ stats.sentCount <= NumFollowers) 
                \/ (stats.ackCount >= MinFollowersForMajority /\ stats.ackCount <= NumFollowers)
           ELSE TRUE

\* Check that committed entries received acknowledgments from a majority of followers.
EntryCommitAckQuorumInv ==
    LET NumServers == Cardinality(Server)
        \* Minimum number of *followers* needed (in addition to the leader)
        \* to reach a majority for committing an entry.
        MinFollowerAcksForMajority == NumServers \div 2
    IN \A key \in DOMAIN entryCommitStats :
        LET stats == entryCommitStats[key]
        IN stats.committed => (stats.ackCount >= MinFollowerAcksForMajority)

\* fake inv to obtain a trace
LeaderCommitted ==
    \E i \in Servers : commitIndex[i] /= 1

=============================================================================