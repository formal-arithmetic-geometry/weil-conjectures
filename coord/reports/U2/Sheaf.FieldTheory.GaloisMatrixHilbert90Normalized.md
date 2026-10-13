## What changed

Replaced the original sorry in `Field.exists_galois_matrix_invariant_basis_normalized`
by invariant-vector spanning, basis extraction, and columnwise matrix extensionality.
The existing signature is byte for byte unchanged. Added two new modules and their nodes:
`Sheaf.FieldTheory.GaloisInvariantVectorsSpan` and
`Sheaf.FieldTheory.SpanningSetUnitMatrix`. Both are now fully proved.
All new imports used only by proofs are plain imports.

The second reader closed the spanning lemma by adapting the proved weighted-averaging
argument from `Field.matrixDescentInvariants_span`. Finite factorization uses the proved
`ProfiniteGrp.exists_openNormalSubgroup_right_invariant`; independence of embeddings
and separation by a linear functional use Mathlib. No coefficients need descent into
the finite intermediate field. The docstring and node now describe this actual proof.

## Proved and sorry left

Original hole closed: `Field.exists_galois_matrix_invariant_basis_normalized`
(node `lem-sc-galois-matrix-hilbert90-normalized`).

New declarations fully proved: `Field.galois_invariant_vectors_span`
(node `lem-sc-galois-invariant-vectors-span`) and
`Matrix.exists_unit_matrix_columns_mem` (node `lem-sc-spanning-set-unit-matrix`).
The second reader closed the former's provisional hole. There are no holes left or added
in the delivery: one original hole closed, zero new holes. No data is taken from an
unproved existence theorem; all witness-producing theorems used here are proved.

## No longer needed

None. The old node had no proof dependencies. No existing import, DAG dependency or
module was pruned. The finite Galois averaging and invariant-basis route is retained.
The original positive-dimension binder is retained, though this proof also covers n=0.

## Where the brief, the DAG or earlier work was wrong

The first worker left invariant-vector spanning open. A proved related argument exists
in `Sheaf.FieldTheory.MatrixDescentInvariantsSpan`; it uses matrix conjugation rather
than this vector action, so it cannot be applied directly, but its weighted sums adapt.
No disputed statement or interface change is needed. Unit `sk-thm-br` has empty realized
lists and this delivery does not bypass a realized unit step.

Edge cases checked mathematically: n=0 is the zero vector space and the empty matrix is
a unit, even for an empty spanning set. For the identity cocycle standard vectors are
invariant. The proof divides by no group order, so positive characteristic is covered.
Extraction uses membership in the original spanning set, without assuming closure under
scalars or requiring zero to belong to that set.

## New nodes

`lem-sc-galois-invariant-vectors-span` records the fully proved finite weighted-averaging
and annihilating-functional argument. Its proof dependency is
`lem-exc-coinduced-functions-open-stabilizer`.

`lem-sc-spanning-set-unit-matrix` records the fully proved extraction of a basis from a
spanning set and its two mutually inverse coordinate matrices. No change records.

## Second reading by U2

1. Compared the existing module with the repository using diff: only proof body and
   plain proof imports change. The sole existing theorem signature is byte for byte
   identical. New signatures match their node records; no definitions are changed.
2. All three modules compile locally without errors or warnings. No sorry, axiom,
   unsafe, opaque, implemented_by, extern or hollow definition remains. Explicit axiom
   #print axioms checks of all three theorems returned exactly propext, Classical.choice
   and Quot.sound; the delivery tool also runs its declaration-wide probe.
3. Read both new statements, their proofs and nodes. Zero dimension, identity cocycles,
   positive characteristic and arbitrary spanning sets are sound. Independent LeanFinder,
   Loogle and grep searches used different wording. The related matrix invariant theorem
   is not an exact match; its proved argument enabled closing the sole provisional hole.
4. The upper proof genuinely combines vector spanning and the proved basis-extraction
   step. Imports serve public signatures or proofs as appropriate. No old dependency
   becomes unused. Read `dag/units/sk-thm-br.json`: realized lists are empty, and the
   finite averaging route is preserved.
5. Node proof steps, proof dependencies and origins agree with the actual Lean.
   New nodes have the required provenance, searches, Lean signatures and unit/chapter.

Changed in this reading: proved `Field.galois_invariant_vectors_span`; added its three
proof-only imports; rewrote its proof docstring and DAG route; corrected this report's
hole accounting from decomposition to one net original hole closed.
