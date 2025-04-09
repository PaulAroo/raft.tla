
Inspired from the HovercRaft paper, and using the Raft spec modified with the third exercise, 

here are the requirements and changes HovercRaft introduces compared to standard Raft, 

aiming for scalability while preserving Raft's core safety and liveness - see attached the design.

You will have to design the Switch component as follows.



Adding the Switch component:

Clients must send requests via a Switch mechanism (like IP Multicast or a middlebox replicating requests) 

that delivers the request payload to all server nodes (leader and followers) simultaneously.



Requirement: The leader node is only responsible for ordering requests by sending fixed-size metadata messages 

(referencing the client request) to followers, not the full request payload. You should separate the payload from client requests.



Requirement: Followers must temporarily store unordered client requests received via Switch multicast and match them 

with the ordering metadata received from the leader.



Bonus Requirement: A recovery mechanism (recovery_request message) must exist for followers to fetch 

missing client requests (due to unreliable multicast) from the leader or other followers.