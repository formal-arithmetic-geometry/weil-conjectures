## What changed
Completed the five remaining proofs in
`Sheaf.RingTheory.AssociatedGradedRing`. The four graded monoid laws now unpack
homogeneous degrees and use quotient induction, the definitional computation of
`LinearMap.liftQ₂` on representatives, and the ring laws of the ambient ring.
A proved private helper `Ideal.associatedGraded_mk_eq` identifies classes in equal
degrees when their representatives agree; it is elementary dependent-equality
bookkeeping, not a new mathematical dependency.

The scalar-action formula rewrites `Algebra.smul_def`, computes the degree-zero
quotient ring map, applies `Ideal.associatedGraded_mul`, and identifies degree
`0 + n` with `n` using the same helper. Updated the definition node's proof and
proof-origin note to describe the completed argument. Existing signatures,
definitions, instances, visibility and imports are unchanged.

## Proved and sorry left
Closed all five holes present in the repository module:

- `Ideal.associatedGraded_gone_mul`;
- `Ideal.associatedGraded_mul_gone`;
- `Ideal.associatedGraded_gmul_assoc`;
- `Ideal.associatedGraded_gmul_comm`;
- `Ideal.associatedGraded_smul`.

Their docstrings cite `lem-weil-pbc-associated-graded-ring-structure`; the module
is recorded by `def-weil-pbc-associated-graded-ring`. No `sorry` remains, no holes
were added, and no statement was split off. The six other proofs mentioned in
the old sandbox report were already proved in the repository baseline and are
retained; they are not counted as holes closed by this delivery.

## No longer needed
None. All three existing Mathlib imports support the constructions in this
module. No Sheaf proof dependency or new module is needed. The definition node
already had an empty `proof_deps` list; it remains empty. No unit statement or
realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong
The earlier sandbox tried to prove `associatedGraded_gone_mul` by `one_mul`
before any monoid structure on the quotient pieces had been constructed. That
attempt does not supply the required structure law and was replaced by quotient
induction. Its report counted six proofs that were already in the repository.
The claim that quotient-lift compatibility prevented completion was too strong:
`liftQ₂` computes definitionally on quotient representatives, and the remaining
degree equalities are handled by a short, proved helper. The DAG's proof note
still described five open holes; the delivered copy now records their proofs.

## Second reading by M3

1. Compared the delivered module with the repository version. Existing public
signatures, definitions, instances, visibility, and imports are byte-for-byte
unchanged; only five proofs and one private helper were added. The DAG node only
records proof and proof-origin updates.

2. Compiled the module with `lcompile.py`; it succeeds with no errors. The file
contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or
`sorryAx`. The added helper is a proved private theorem, and the proof uses only
ordinary ring and quotient facts.

3. Checked each declaration against the repository and searched Mathlib and the
Sheaf sources for an existing associated-graded construction or equivalent
helper. No split-off statements or new public nodes were added; all five target
proofs remain exactly the original statements.

4. Read the proof route and imports. Quotient induction is the shortest route for
the graded monoid laws, `liftQ₂` computes on representatives, and the scalar
formula uses the existing homogeneous multiplication theorem. Every existing
import is still used, and no unit step is bypassed.

5. Checked the definition node's proof and proof dependencies against the Lean
proof. The node now describes quotient induction and representative calculations,
with no new proof dependency; the unit route remains realized.

Changed during this second reading: no Lean statements or definitions. Added
this review section and retained the node's proof/proof-origin update.
