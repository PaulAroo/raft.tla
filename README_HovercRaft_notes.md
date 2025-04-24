
## Notes on Project progress

### 07 / 04 / 2025
------------------

Understanding the requirements of the first exercise

- Add a switch component
- Adapt spec such that switch handles client request
  - disseminates client request to all servers
  - keeps it's own log
  - has it's own append entries actions
  - entries in the switch's log add an extra payload field 

- Servers (both leaders and followers) have a cache (to store the entries received from switch)

- The leader also sends the client request to followers (just metadata), the follower check that that request exists in the followers cache unordered, if it exist, respond to leader otherwise failed

### 09 / 04 / 2025
-------------------

First steps towards implementation
- Add an action for switch to handle (accept and log) client request
- Update variables and state transition formulas to match (MyInit, MyNext)
- unanswered questions:
  - allow logging the same value v again just because the leader's term changed?
  - how do I keep track of the index to the switch's log, in order to determine what needs to be sent next (adding a combined action where a switch adds entry to it's log and sends should solve this problem?)

### 19 / 04 / 2025
-------------------

- Added VARIABLE `switchNextIndex`: A function mapping each Server s to the next index in switchLog that the Switch needs to send to that specific server.
- Added a new message type `AppendSwitchEntriesRequest`
- Created action `SwitchAppendEntries(s)`:
  - Triggered in `MyNext` for a specific target server `s`
  - Uses `switchNextIndex[s]` to determine the entry index to send from `switchLog`.
  - Constructs a `AppendSwitchEntriesRequest` message containing the term, value, and payload.
  - Optimistically increments `switchNextIndex[s]`
- Created handler action `HandleAppendSwitchEntryRequest`
  - primarily updates server cache with entry
- Updated the explicit set of message types handled by the Receive trigger in MyNext to include AppendSwitchEntriesRequest


### 23 / 04 / 2025
-------------------
- Added new actions
  - `LeaderProposeFromCache`: Leader moves an entry from its cache to it's log, AppendEntries actions then ensures the metadata from this entry is sent to the followers
  - `NewHandleAppendEntriesRequest`: modified version of `HandleAppendEntriesRequest` where a follower handles Metadata related request from the leader (check its cache for matching entry before sending a successful response)
  - Updated `MyInit` and `MyNext` as needed