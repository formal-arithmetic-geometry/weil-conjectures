## What changed

The item now constructs the normalized unit isomorphism and combines the left and right representative calculations. Two focused representative theorem modules were added; their proofs remain split for follow-up work.

## Proved and sorry left

One original hole is closed: `CategoryTheory.RingedForgetTensorTransposition.ringed_forget_tensor_unit_representatives`. Two holes are added, so this is a decomposition, with net hole change +1, not a completed proof of the unit calculation. The two component calculations remain as named split holes: `ringed_forget_tensor_left_representatives` in `lem-sf-ringed-forget-tensor-left-representatives`, and `ringed_forget_tensor_right_representatives` in `lem-sf-ringed-forget-tensor-right-representatives`.

## No longer needed

No imports or declared dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong
An initial draft incorrectly quantified over an arbitrary unit isomorphism. This was repaired before delivery: both split statements now contain the exact normalized composite, with no arbitrary unit map.

The original proof plan hides two independent representative calculations. They are recorded as separate component nodes so they can be proved independently.

## New nodes

`lem-sf-ringed-forget-tensor-left-representatives` and `lem-sf-ringed-forget-tensor-right-representatives` are the left and right unit component calculations, respectively.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
