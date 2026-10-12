## What changed

Completed `AlgebraicGeometry.descend_qc_open_fg_subalgebra`. The proof introduces the predicate that an
open is the pullback of a compact open over a finitely generated subalgebra, proves it for the empty open
and proves closure under finite unions using `Subalgebra.sup`, quasi-compact transition maps, and
`baseChangeMap_comp`. The existing pointwise construction is imported from
`Sheaf.AlgebraicGeometry.DescendedQCNeighborhood`. The proof then applies compactness of the input open
to obtain a finite subcover and combines the local witnesses. Added the new node
`lem-weil-pbc-descended-qc-neighborhood` for the imported pointwise construction.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.descend_qc_open_fg_subalgebra`,
by a complete Lean proof from the new pointwise statement. This is a decomposition:
one hole closed and one lower hole added, net zero; it is not a sorry-free proof. The imported theorem
`AlgebraicGeometry.exists_descended_qc_neighborhood` remains `sorry`, recorded by node
`lem-weil-pbc-descended-qc-neighborhood`; this is a strict pointwise part of the argument, not a restatement
of the target. No new sorry was added to the item's module.

## No longer needed

No imports or modules are pruned. The original direct proof dependencies
`lem-weil-pbc-open-fibre-product` and `lem-weil-pbc-fibre-product-affine-spectra` are now
transitive dependencies through `lem-weil-pbc-descended-qc-neighborhood`; they remain needed.
The proof-only import `Mathlib.AlgebraicGeometry.Morphisms.Affine` is needed for the
quasi-compactness instance of spectrum maps (removing it was tested and failed).

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's local theorem was correct and compiled, but had no DAG node or delivery report. The
DAG's four-step global proof was reorganized into a pointwise neighborhood lemma, finite-union closure, and
finite compactness subcover; this preserves the Tag 0388 route and does not assume quasi-separatedness.

The authorized delivery dry run was run twice after compilation/probes. Both runs
failed with `(a) uncommitted changes in the working tree`, despite deliver3.py
creating the delivery commit itself. The final run reported only that tool-state
failure and the expected missing second reading. No push was attempted. The
worker may not edit the delivery scripts or use git directly in the read-only
clone; the launcher/tool maintainer must resolve this failure before the second
reader delivers.

## New nodes

`lem-weil-pbc-descended-qc-neighborhood`: pointwise compact-neighborhood descent used in the final finite
subcover argument. Its Lean module is `Sheaf.AlgebraicGeometry.DescendedQCNeighborhood`.

Edge cases checked: the empty open is proved using the bottom subalgebra and empty
compact open; an empty scheme has no pointwise obligation. For A = k the coefficient
subalgebra may be bottom. Arbitrary V is permitted in the local lemma; compactness
is used only for the final subcover, never for chart intersections. Maps between
coefficient stages need not be surjective or flat: only affineness and its stability
under base change are used. The canonical projection in the original signature is
unchanged, and the final equality with the helper projection is proved by rfl.

Source read: https://stacks.math.columbia.edu/tag/0388 (the local varieties.tex is
not present on this machine). The new lemma follows its single-principal-open
construction. LeanSearch returned HTTP 500 and is recorded as unavailable.
LeanFinder, Loogle, Mathlib grep, and blueprint searches found no exact pointwise
statement; `exists_preimage_eq` requires a cofiltered limit presentation.
No existing definitions or public signatures were changed, so no change records
or forced adaptations are needed.

## Second reading by C3

1. **Statements unchanged.** Compared the delivered item module with the repository version. The existing
   target signature is byte-for-byte unchanged; the added declaration is in a new module and its node
   records the exact signature.
2. **Proof and truth.** Compiled both sandbox modules successfully. The target proof uses only the
   pointwise neighborhood lemma, finite-union closure, and compactness of the given open. The remaining
   `sorry` is exactly the named theorem `AlgebraicGeometry.exists_descended_qc_neighborhood`, with a
   matching node and source; no definition contains `sorry`.
3. **New statement.** Checked the pointwise lemma's hypotheses and conclusion against the finite-principal-
   open argument of Stacks Tag 0388, including empty opens and arbitrary (not compact) ambient opens.
   It is strictly weaker than the target and is needed for the finite-subcover proof.
4. **Pruning and imports.** The route retains the unit's descended-open step. The proof-only affine
   morphism import is needed for quasi-compactness of transition maps; no import or proof dependency can
   be removed.
5. **DAG agreement.** The item's node proof, proof dependencies, and proof origin match the Lean route;
   the new node and module metadata match the split-off theorem. No unit statement or realized route was
   changed.

Changed during second reading: added this review record only; no Lean code or DAG declarations were altered.
