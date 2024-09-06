---------------------- MODULE reader_writer -----------------------
(* define a spec for a writer of messages to eg a queue and a reader that      *)
(* reads them back again.                                                      *)

EXTENDS Naturals, Sequences, TLC

CONSTANTS alphabet, num_messages
VARIABLES messages_sent, num_received

(* name the variables                                                           *)
vars == << messages_sent, num_received >>

(* The message format for the channel is a list of messages from the alphabet   *)
possible_queues == UNION { [ 1..n -> alphabet ] : n \in 0..num_messages }


num_sent == Len(messages_sent)

(* Type invariants                                                            *)
MessageType == messages_sent \in possible_queues
CountersType ==
    /\ num_sent \in 0..num_messages
    /\ num_received \in 0..num_sent
TypeOK == MessageType /\ CountersType


(* Initial state is null *)
Init == /\ messages_sent = <<>>
        /\ num_received = 0

(* Predicates on state: *)
Done == /\ num_sent = num_messages
        /\ num_received = num_messages
Can_write == num_sent < num_messages
Can_read == num_received < num_sent


(* State can evolve through Reading or writing messages *)
Read_Msg == /\ Can_read
            /\ num_received' = num_received + 1
            /\ UNCHANGED messages_sent

Write_Msg ==
    /\ Can_write
    /\ \E msg \in alphabet:
        messages_sent' = Append(messages_sent, msg)
    /\ UNCHANGED num_received

Next == \/ Read_Msg
        \/ Write_Msg
        \/ (Done /\ UNCHANGED vars)

(* Specification: Include weak fairness conditions indicating that writes and reads will
   eventually progress
*)
Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Read_Msg)
        /\ WF_vars(Write_Msg)

NoFairSpec == /\ Init
              /\ [][Next]_vars


Eventually_Done == <>Done

(* Test Prints *)
\* messages_init == [x \in 1..num_messages |-> ]
\* ASSUME(PrintT(<< "messages_init",  messages_init >>))
\* ASSUME(PrintT(<< "queues", possible_queues >>))
\* ASSUME(PrintT(<<"head_queue", head(<< "A", "B", "C">>)>>))
\* ASSUME(PrintT(<<"head_queue", Tail(<<"A","B","C">>)>>))
===================================================================
