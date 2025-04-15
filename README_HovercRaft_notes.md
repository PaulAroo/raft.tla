
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
------------------

First steps towards implementation
- Add an action for switch to handle (accept and log) client request
- Update variables and state transition formulas to match (MyInit, MyNext)
- unanswered questions:
  - allow logging the same value v again just because the leader's term changed?
  - how do I keep track of the index to the switch's log, in order to determine what needs to be sent next (adding a combined action where a switch adds entry to it's log and sends should solve this problem?)