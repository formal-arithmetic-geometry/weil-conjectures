## What changed

Proved `AlgebraicGeometry.exists_nonempty_open_isFinite_restrict_of_isProjective_generic_dim_le_zero`
in `Sheaf.AlgebraicGeometry.ProjectiveGenericallyFinite` without changing its signature or public
imports. The proof adapts the already-proved argument in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.FiniteMorphism.exists_isFinite_morphismRestrict_of_generic_fibre`
to the arbitrary fraction field K in this statement. It uses properness under base change,
Mathlib's zero-dimensional locally Artinian criterion, compactness, and point lifting to show
that an ordinary fibre is finite. Mathlib's
`exists_isFinite_morphismRestrict_of_finite_preimage_singleton` then supplies the required open.
The open is nonempty because it contains the image of a point of Spec K.

Updated the theorem's proof docstring and the node's proof, proof dependencies, and proof origin
to describe this actual route. Removed the two obsolete tool-use approvals from this node;
no approvals were added. The unit's statement and its realized steps are untouched.

Searches: Lean Finder returned properness and finite-type ingredients rather than the full
statement. Loogle and grep found the exact proper finite-fibre neighbourhood theorem in
Mathlib.AlgebraicGeometry.ZariskisMainTheorem. Reading the source library found the analogous
proved projective-embedding statement and its reusable argument. The proof supports empty and
nonreduced generic fibres: local Artinianness and compactness imply finiteness without any
nonemptiness assumption on the generic fibre itself.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.exists_nonempty_open_isFinite_restrict_of_isProjective_generic_dim_le_zero`
(node `lem-fin-projective-generically-finite`). Added 0 holes; split off 0 statements. No sorry
remains in the delivered module. The first completed proof compiled cleanly in 2.7 seconds.
Final compilation and the delivery probe check the cleaned version and its axioms.

## No longer needed

Removed these proof imports:

- `Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange`: projectivity of the pullback is
  unnecessary; properness of f and its stability under base change give finite type and
  compactness directly. Node `lem-pc-projective-base-change` is no longer a proof dependency.
- `Sheaf.AlgebraicGeometry.ProperFiniteFibreFiniteNeighbourhood`: Mathlib already proves its
  conclusion with no locally Noetherian hypothesis. Node
  `thm-sc-proper-finite-fibre-finite-neighbourhood` is replaced by the existing Mathlib-backed
  node `lem-trf-proper-finite-fibre-finite-near`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: its needed public declarations already
  come through the unchanged public import of Morphisms.Projective.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and
  `Mathlib.AlgebraicGeometry.Noetherian`: their required APIs are already supplied by the
  retained public imports and the proof imports Artinian and ZariskisMainTheorem.

The explicit residue-field identification and fibre homeomorphism from
`def-pc-scheme-fibre` are unnecessary in the proof: point lifting to the pullback suffices.
The separate locally Noetherian-base step `pqf-def-locnoeth` is unnecessary for the stronger
Mathlib neighbourhood theorem. These two nodes leave the direct proof dependency list;
the statement dependencies and all public imports are unchanged.

The two removed Sheaf modules are unused by this proof. This report makes no claim that they
are globally unreachable through other parents; the maintainer's import-closure accounting
will determine that.

## Where the brief, the DAG or earlier work was wrong

The earlier generic-open proof did not find Mathlib's exact finite-fibre neighbourhood theorem
in ZariskisMainTheorem. Its locally Noetherian-base step and its use of the unproved Sheaf
version were therefore avoidable. The earlier projective-base-change step was stronger than
needed: properness under base change is already proved in Mathlib. The original statement is
correct and unchanged. No definition repair, consumer adaptation, change record, or new node
is needed.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
