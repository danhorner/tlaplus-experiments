
--------- MODULE goat_cabbage --------
EXTENDS TLC, Integers, FiniteSets
VARIABLES 
    left_bank,
    right_bank,
    bank,
    boat

Animals == {"goat", "wolf", "cabbage"}
Banks == {"right", "left"}
\* Animals == {"eagle",  "bear"}

Init == /\ left_bank= Animals
        /\ right_bank = {}
        /\ bank = "left"
        /\ boat = {}

Unsafe(S) == 
   \/  /\ "wolf" \in S
       /\ "goat" \in S
   \/  /\ "goat" \in S
       /\ "cabbage" \in S

TypeInvariant == /\ left_bank \subseteq Animals
                 /\ right_bank \subseteq Animals
                 /\ boat \subseteq Animals
                 /\ bank \in Banks

Unsolved == right_bank # Animals

Transfer(src, dest) == 
\E animals \in SUBSET Animals: 
  /\ animals \subseteq src
  /\ dest' = dest \union animals
  /\ src' = src \ animals
  /\ {} = dest \intersect animals

LeftBankActivity ==
  /\ ~Unsafe(right_bank)
  /\ bank' = "left"
  /\ UNCHANGED right_bank
  /\ \/ Transfer(left_bank, boat)
     \/ Transfer(boat, left_bank)

RightBankActivity ==
  /\ ~Unsafe(left_bank)
  /\ bank' = "right"
  /\ UNCHANGED left_bank
  /\ \/ Transfer(right_bank, boat)
     \/ Transfer(boat, right_bank)

Next == 
/\ \/ LeftBankActivity
   \/ RightBankActivity
/\ Cardinality(boat') <= 1


ASSUME Unsafe({"goat", "cabbage"})
ASSUME Unsafe({"wolf", "goat"})

================