------------ MODULE ring_buffer -----------
EXTENDS Naturals, Sequences, TLC

CONSTANT alphabet, num_messages, buffer_size, NULL


possible_queues == UNION { [ 1..n -> alphabet ] : n \in 0..num_messages }

(* Let's figure out how to implement a producer/consumer queue in PlusCal
*)

(* --algorithm RingBuffer
 variables
  messages \in possible_queues;
  buffer = [x \in 1..buffer_size |-> NULL];
  messages_read = <<>>;
  empty = TRUE;
  next_read = 1;
  next_write = 1;

  define
   full == ~empty /\ next_read = next_write
   size == IF empty
          THEN 0
          ELSE IF next_write > next_read
          THEN next_write - next_read
          ELSE buffer_size + next_write - next_read
    Eventually_Complete == <>(Len(messages_read) = Len(messages))
    Reads_Accurate == \A x \in 1..Len(messages_read) : messages_read[x] = messages[x]
  end define;

 fair+ process writer="writer"
   variables
     messages_written = 0;

   begin
 WR_BEGIN:
     while messages_written < Len(messages) do
 WR_WAIT:
     await ~full;
 WR_A:
     buffer[next_write] := messages[messages_written + 1];
 WR_B:
     empty := FALSE;
     next_write := ( next_write % buffer_size ) + 1;
     messages_written := messages_written + 1;
     end while;
 end process;

 fair+ process reader="reader"
 begin
 RD_BEGIN:
   while Len(messages_read) < Len(messages) do
 RD_WAIT:
   await ~empty;
 RD_A:
   messages_read := Append(messages_read, buffer[next_read]);
 RD_B:
   if size = 1 then
     empty := TRUE;
   end if;
   next_read := ( next_read % buffer_size ) + 1;
   end while;
 end process;

end algorithm; *)


\* BEGIN TRANSLATION
VARIABLES messages, buffer, messages_read, empty, next_read, next_write, pc

(* define statement *)
full == ~empty /\ next_read = next_write
size == IF empty
       THEN 0
       ELSE IF next_write > next_read
       THEN next_write - next_read
       ELSE buffer_size + next_write - next_read
 Eventually_Complete == <>(Len(messages_read) = Len(messages))
 Reads_Accurate == \A x \in 1..Len(messages_read) : messages_read[x] = messages[x]

VARIABLE messages_written

vars == << messages, buffer, messages_read, empty, next_read, next_write, pc,
           messages_written >>

ProcSet == {"writer"} \cup {"reader"}

Init == (* Global variables *)
        /\ messages \in possible_queues
        /\ buffer = [x \in 1..buffer_size |-> NULL]
        /\ messages_read = <<>>
        /\ empty = TRUE
        /\ next_read = 1
        /\ next_write = 1
        (* Process writer *)
        /\ messages_written = 0
        /\ pc = [self \in ProcSet |-> CASE self = "writer" -> "WR_BEGIN"
                                        [] self = "reader" -> "RD_BEGIN"]

WR_BEGIN == /\ pc["writer"] = "WR_BEGIN"
            /\ IF messages_written < Len(messages)
                  THEN /\ pc' = [pc EXCEPT !["writer"] = "WR_WAIT"]
                  ELSE /\ pc' = [pc EXCEPT !["writer"] = "Done"]
            /\ UNCHANGED << messages, buffer, messages_read, empty, next_read,
                            next_write, messages_written >>

WR_WAIT == /\ pc["writer"] = "WR_WAIT"
           /\ ~full
           /\ pc' = [pc EXCEPT !["writer"] = "WR_A"]
           /\ UNCHANGED << messages, buffer, messages_read, empty, next_read,
                           next_write, messages_written >>

WR_A == /\ pc["writer"] = "WR_A"
        /\ buffer' = [buffer EXCEPT ![next_write] = messages[messages_written + 1]]
        /\ pc' = [pc EXCEPT !["writer"] = "WR_B"]
        /\ UNCHANGED << messages, messages_read, empty, next_read, next_write,
                        messages_written >>

WR_B == /\ pc["writer"] = "WR_B"
        /\ empty' = FALSE
        /\ next_write' = ( next_write % buffer_size ) + 1
        /\ messages_written' = messages_written + 1
        /\ pc' = [pc EXCEPT !["writer"] = "WR_BEGIN"]
        /\ UNCHANGED << messages, buffer, messages_read, next_read >>

writer == WR_BEGIN \/ WR_WAIT \/ WR_A \/ WR_B

RD_BEGIN == /\ pc["reader"] = "RD_BEGIN"
            /\ IF Len(messages_read) < Len(messages)
                  THEN /\ pc' = [pc EXCEPT !["reader"] = "RD_WAIT"]
                  ELSE /\ pc' = [pc EXCEPT !["reader"] = "Done"]
            /\ UNCHANGED << messages, buffer, messages_read, empty, next_read,
                            next_write, messages_written >>

RD_WAIT == /\ pc["reader"] = "RD_WAIT"
           /\ ~empty
           /\ pc' = [pc EXCEPT !["reader"] = "RD_A"]
           /\ UNCHANGED << messages, buffer, messages_read, empty, next_read,
                           next_write, messages_written >>

RD_A == /\ pc["reader"] = "RD_A"
        /\ messages_read' = Append(messages_read, buffer[next_read])
        /\ pc' = [pc EXCEPT !["reader"] = "RD_B"]
        /\ UNCHANGED << messages, buffer, empty, next_read, next_write,
                        messages_written >>

RD_B == /\ pc["reader"] = "RD_B"
        /\ IF size = 1
              THEN /\ empty' = TRUE
              ELSE /\ TRUE
                   /\ empty' = empty
        /\ next_read' = ( next_read % buffer_size ) + 1
        /\ pc' = [pc EXCEPT !["reader"] = "RD_BEGIN"]
        /\ UNCHANGED << messages, buffer, messages_read, next_write,
                        messages_written >>

reader == RD_BEGIN \/ RD_WAIT \/ RD_A \/ RD_B

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == writer \/ reader
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(writer)
        /\ SF_vars(reader)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

reader_writer == INSTANCE reader_writer  WITH
     num_received <- Len(messages_read),
     messages_sent <- SubSeq(messages, 1, messages_written)

\* Check this by checking temporal property reader_writer!Spec

\* We check the ring buffer against the reader writer spec without
\* the fairness conditions that guarantee progress
\* This beause the reader writer spec assumes that all num_messages
\* messages will be sent, but ring buffer also tries cases where
\* fewer messages will be sent
\*
\* ReaderWriterSpec == reader_writer!Spec
ReaderWriterSpec == reader_writer!NoFairSpec
THEOREM Spec => ReaderWriterSpec

============================================
