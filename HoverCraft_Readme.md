
## 07 / 04 / 2025

Understanding the requirements of the first exercise

- Add a switch component
- Adapt spec such that switch handles client request
  - disseminates client request to all servers
  - keeps it's own log
  - has it's own append entries actions
  - entries in the switch's log add an extra payload field 

- Servers (both leaders and followers) have a cache (to store the entries received from switch)

the leader also sends the client request to followers (just metadata), the follower check that that request exists in the followers cache unordered, if it exist, respond to leader otherwise failed
