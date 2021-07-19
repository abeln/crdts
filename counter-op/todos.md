Send acks directly instead of going through out queue.

In receive loop:
  - receive msg
  - compare VC projections
  - if sender smaller, it's network dup, so throw away
  - if equal, then already applied so ack again
  - if it's larger by exactly one, then keep it and ack it
  - if it's larger by more than one, can't happen so assert false
  - all acks in receive loop

In apply loop:
  - remove acks from apply loop

keep stop-and-wait

test dropped messages in send
test via script multiple operations




