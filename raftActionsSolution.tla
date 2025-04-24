---------------------------- MODULE raftActionsSolution ----------------------------

EXTENDS raftInit

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
           entries == << entry >>
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
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, maxc, leaderCount>>

\* Modified HoverCraft AppendEntries
AppendMetaDataEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ Len(log[i]) > 0  \* Only proceed if the leader has entries to send
    /\ nextIndex[i][j] <= Len(log[i])
    /\ LET entryIndex == nextIndex[i][j]
           leaderLogEntry == log[i][entryIndex] \* Get the full entry from leader's log

           \* <<< THE CRUCIAL CHANGE >>>
           \* Explicitly create a *new* record with ONLY metadata
           metadataEntry == [term |-> leaderLogEntry.term,
                             value |-> leaderLogEntry.value]
           \* Put the metadata-only record into the sequence
           entriesToSend == << metadataEntry >>

           prevLogIndex == entryIndex - 1
           prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex].term ELSE 0
           entryKey == <<entryIndex, leaderLogEntry.term>>
       IN
         \* Send the message with mentries containing only the metadata record
         /\ Send([mtype          |-> AppendEntriesRequest,
                  mterm          |-> currentTerm[i],
                  mprevLogIndex  |-> prevLogIndex,
                  mprevLogTerm   |-> prevLogTerm,
                  mentries       |-> entriesToSend,  \* << Now contains metadata only
                  mcommitIndex   |-> Min({commitIndex[i], prevLogIndex}),
                  msource        |-> i,
                  mdest          |-> j])

         /\ entryCommitStats' =
            IF entryKey \in DOMAIN entryCommitStats /\ ~entryCommitStats[entryKey].committed
            THEN [entryCommitStats EXCEPT ![entryKey].sentCount = @ + 1]
            ELSE entryCommitStats

    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, maxc, leaderCount, switchVars, serverCache>>

SwitchAcceptAndLogRequest(leader, v) ==
    /\ maxc < MaxClientRequests
    /\ LET entryTerm == currentTerm[leader]
           entry == [term |-> entryTerm, value |-> v, payload |-> v]
           entryExists == \E index \in DOMAIN switchLog : switchLog[index].value = v /\ switchLog[index].payload = v /\ switchLog[index].term = entryTerm
          \*  newLog == IF entryExists THEN switchLog ELSE Append(switchLog, entry)
       IN
        /\ switchLog' = IF entryExists THEN switchLog ELSE Append(switchLog, entry)
        /\ maxc' = IF entryExists THEN maxc ELSE maxc + 1

    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, entryCommitStats, leaderCount, serverCache, switchNextIndex>>


\* Switch attempts to send the next log entry to a specific server 's'.
SwitchAppendEntries(s) ==
    /\ Len(switchLog) > 0  \* Only proceed if the switch has entries to send
    /\ switchNextIndex[s] <= Len(switchLog)
    /\ LET nextLogIdxToSend == switchNextIndex[s] \* Index in switchLog to send to server 's'
           entry == switchLog[nextLogIdxToSend]
           entries == << entry >>

      IN Send([mtype          |-> AppendSwitchEntriesRequest,
               mentries       |-> entries,
               msource        |-> Switch,
               mterm          |-> entry.term,
               mdest          |-> s])


       /\ switchNextIndex' = [switchNextIndex EXCEPT ![s] = @ + 1]
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, entryCommitStats, leaderCount, serverCache, switchLog, maxc>>

\* Server s receives an AppendEntries request from the Switch
HandleAppendSwitchEntryRequest(s, m) ==
    \/ /\ m.mterm < currentTerm[s]  \* Stale message from a previous term
       \* Ignore stale messages, just discard them.
       /\ Discard(m)
       /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, entryCommitStats, leaderCount, switchLog, switchNextIndex, maxc, serverCache>>

    \/ /\ m.mterm = currentTerm[s]
       /\ LET receivedEntry == m.mentries[1]
          IN
             /\ serverCache' = [serverCache EXCEPT ![s] = @ \cup {receivedEntry}]
             /\ Discard(m)

       \* State unchanged except for serverCache and messages (handled by Discard)
       /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, entryCommitStats, leaderCount, switchVars, maxc>>


\* Action: Leader 'i' proposes an entry from its cache by adding it to its own log.
LeaderProposeFromCache(i) ==
    /\ state[i] = Leader
    \* Ensure there's something in the cache to propose
    /\ serverCache[i] /= {}
    /\ LET
           \* Non-deterministically choose an entry from the leader's cache
           cachedEntry == CHOOSE ce \in serverCache[i] : TRUE
           newLogEntry == [ term    |-> currentTerm[i],
                            value   |-> cachedEntry.value,
                            payload |-> cachedEntry.payload ]

           \* Check if this value is already somewhere in the log (duplicate prevention)
           valueAlreadyInLog == \E idx \in DOMAIN log[i] : log[i][idx].value = newLogEntry.value
       IN
         \* Only proceed if the value isn't already logged
         /\ ~valueAlreadyInLog
         /\ LET newEntryIndex == Len(log[i]) + 1
                newEntryKey == <<newEntryIndex, newLogEntry.term>>
            IN
              \* Effect 1: Append the official entry to the leader's log
              /\ log' = [log EXCEPT ![i] = Append(log[i], newLogEntry)]

              \* Effect 2: Initialize commit stats for the new log entry
              /\ entryCommitStats' =
                   entryCommitStats @@ (newEntryKey :> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ])

              \* Remove the chosen entry from the leader's cache (not sure if we want this)
            \*   /\ serverCache' = [serverCache EXCEPT ![i] = @ \ {cachedEntry}]

         \* Ensure other core state is untouched by this specific action
         /\ UNCHANGED <<messages, currentTerm, state, votedFor, commitIndex, nextIndex, matchIndex, leaderCount, maxc, switchVars, serverCache, voterLog, votesGranted, votesResponded>>
         \* Note: 'log', 'entryCommitStats', 'serverCache' are explicitly changed above.

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* reject request
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \lnot logOk
             /\ Reply([mtype           |-> AppendEntriesResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mmatchIndex     |-> 0,
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ UNCHANGED <<serverVars, logVars>>
          \/ \* return to follower state
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages>>
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
                       /\ UNCHANGED <<serverVars, log>>
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
                       /\ UNCHANGED <<serverVars, commitIndex, messages>>
                   \/ \* no conflict: append entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) = m.mprevLogIndex
                       /\ log' = [log EXCEPT ![i] =
                                      Append(log[i], m.mentries[1])]
                       /\ UNCHANGED <<serverVars, commitIndex, messages>>
       /\ UNCHANGED <<candidateVars, leaderVars, instrumentationVars>> \* entryCommitStats unchanged on followers

\* Modified: Follower i handles AppendEntries METADATA request from leader j.
NewHandleAppendEntriesRequest(i, j, m) ==
    LET \* Standard Raft log consistency check
        logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN
       \* Standard Raft term checks and state updates
       /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* Reject request (standard Raft conditions)
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \lnot logOk
             /\ Reply([mtype           |-> AppendEntriesResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mmatchIndex     |-> 0, \* Indicate failure at prevLogIndex
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ UNCHANGED <<serverVars, logVars, serverCache>> \* Cache unchanged on rejection
          \/ \* Step down if Candidate (standard Raft)
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages, serverCache>>
          \/ \* Process request (term ok, state follower, log consistent up to prev)
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                IN \/ \* Request has no new entries (standard heartbeat)
                       /\ m.mentries = << >>
                       \* Update commit index based on leader's signal
                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], m.mcommitIndex})]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex, \* Matched up to prev index
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, log, serverCache>>
                   \/ \* Request HAS new metadata entries
                       /\ m.mentries /= << >>
                       /\ LET \* <<< HOVERCRAFT CHANGE >>> Check Follower Cache
                              entryMetadata == m.mentries[1] \* Extract metadata sent by leader
                              \* Find matching entry in cache based on VALUE and TERM from metadata
                              \* (Term check ensures we match data associated with the correct proposal term)
                              MatchingCacheEntries == { ce \in serverCache[i] :
                                                          /\ ce.value = entryMetadata.value
                                                          /\ ce.term = entryMetadata.term }
                              cacheHit == (MatchingCacheEntries /= {})
                          IN \/ /\ ~cacheHit \* Cache MISS: Data not found
                                 /\ Reply([mtype           |-> AppendEntriesResponse,
                                           mterm           |-> currentTerm[i],
                                           msuccess        |-> FALSE,
                                           \* Failure implies mismatch at prevLogIndex, or data missing.
                                           \* Leader will retry prevLogIndex based on Raft logic.
                                           mmatchIndex     |-> 0,
                                           msource         |-> i,
                                           mdest           |-> j],
                                           m)
                                 /\ UNCHANGED <<serverVars, logVars, serverCache>>
                             \/ /\ cacheHit \* Cache HIT: Data found
                                 /\ LET MatchingCacheEntry == CHOOSE ce \in MatchingCacheEntries : TRUE
                                        \* Construct full entry using metadata term/value and cache payload
                                        fullEntryToLog == [ term    |-> entryMetadata.term,
                                                            value   |-> entryMetadata.value,
                                                            payload |-> MatchingCacheEntry.payload ]
                                    IN \/ \* Conflict: Entry exists at index, but term differs
                                           /\ Len(log[i]) >= index
                                           /\ log[i][index].term /= fullEntryToLog.term
                                           \* Truncate follower's log (standard Raft conflict handling)
                                           /\ LET newLog == SubSeq(log[i], 1, index - 1)
                                              IN log' = [log EXCEPT ![i] = newLog]
                                           \* Remove entry from cache *after* successful processing? Maybe not here.
                                           /\ UNCHANGED <<serverVars, commitIndex, messages, serverCache>>
                                       \/ \* No conflict: Append or entry already matches
                                           /\ \/ Len(log[i]) = index - 1 \* Ready to append
                                              \/ /\ Len(log[i]) >= index   \* Entry might already be here
                                                 /\ log[i][index].term = fullEntryToLog.term
                                                 \* (No need to check value, Raft guarantees if term/index match, value matches)
                                           \* Append if missing, otherwise log is unchanged
                                           /\ log' = IF Len(log[i]) = index - 1
                                                     THEN [log EXCEPT ![i] = Append(log[i], fullEntryToLog)]
                                                     ELSE log
                                           \* Update commit index based on leader's signal
                                           /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], m.mcommitIndex})]
                                           \* Send success response
                                           /\ Reply([mtype           |-> AppendEntriesResponse,
                                                     mterm           |-> currentTerm[i],
                                                     msuccess        |-> TRUE,
                                                     mmatchIndex     |-> index, \* Success up to this new index
                                                     msource         |-> i,
                                                     mdest           |-> j],
                                                     m)
                                           /\ UNCHANGED <<serverVars, serverCache>>

       /\ UNCHANGED <<candidateVars, leaderVars, entryCommitStats, leaderCount, switchVars, maxc, serverCache>> \* Switch state unaffected


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
    /\ UNCHANGED <<serverVars, candidateVars, logVars, maxc, leaderCount, switchVars, serverCache>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :
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
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, maxc, leaderCount, switchVars, serverCache>>

\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars>>

=============================================================================
\* Created by Ovidiu-Cristian Marcu
