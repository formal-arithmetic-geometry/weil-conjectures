## What changed

The sandbox copy of `Sheaf.Paper.CartierEquality` contains the complete proof of
`cartier_equality`, with the existing imports and statement unchanged. This proof
is already present on the base branch (commit `e6280b231`); no source edit is
needed for this delivery.

## Proved and sorry left

The declaration `cartier_equality` is proved with no `sorry` remaining. No new
holes were added.

## No longer needed

None. All imports in the existing proof are used by its statement or proof.

## Where the brief, the DAG or earlier work was wrong

The item was already proved and landed on the base branch before this worker was
dispatched. The DAG statement and proof agree with the existing module.


## Second reading by D2

1. Compared the delivered module with the repository version. The theorem signature and all declarations are byte-for-byte unchanged; the only proof difference removes an unused `have := hA`.
2. Compiled `Sheaf.Paper.CartierEquality` with `lcompile.py`; it succeeds with no errors or warnings. An axiom probe reports only `propext`, `Classical.choice`, and `Quot.sound`, and there are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations.
3. The existing theorem is the sole declaration and no statements were split off or added. Its statement is unchanged and agrees with the DAG node; no new node is needed.
4. The proof follows the existing Cartier equality route through the finite transcendence basis, complete-intersection model, cotangent model, and rank-nullity. All imports remain needed by the statement or proof; no additional shorter route was identified.
5. The unit route and DAG proof dependencies are preserved. The only change made was deleting the unused local assignment `have := hA` from the proof.

Changed: removed the unused local assignment and recorded this second reading.
