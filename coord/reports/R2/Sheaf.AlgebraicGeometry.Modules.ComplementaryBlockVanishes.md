## What changed

Preserved the signature of `complementary_block_eq_zero_of_rank_le` and replaced its sorry
with a proof combining pointwise residue-matrix vanishing and reduced-scheme detection.
Added two proof-only imports: `ComplementaryBlockResidueVanishes` and
`FreeMapResidueDetection`. The latter contains a complete proof using Mathlib's
basic-open/evaluation and reduced-section criteria, plus the existing free-sheaf
coordinate identities and free-generator API. Its private helper is fully proved.
No existing definitions, signatures, or public imports changed.

Removed the earlier attempt's uncommitted `ComplementaryBlockFiberEquality` module and
node; its conclusion was equivalent to the entire target. They are not delivered.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.complementary_block_eq_zero_of_rank_le`.
This is a decomposition, not a sorry-free proof of the geometric theorem: one original
hole closed and one strictly smaller hole added, for net zero holes.

Proved without sorry
`AlgebraicGeometry.Scheme.Modules.free_map_eq_zero_of_residue_evaluations`
(node `lem-pc-free-map-residue-detection`) and its private helper
`unit_map_eq_zero_of_top_one`. This completes the reducedness and free-sheaf extensionality
steps of the original plan, including empty schemes and empty complementary index sets.

The only sorry left in the delivery is
`AlgebraicGeometry.Scheme.Modules.complementary_block_residue_eq_zero_of_rank_le`
(node `lem-pc-complementary-block-residue-vanishes`). It proves matrix vanishing at one
point, has no reducedness hypothesis, and uses only a rank bound at that point. It covers
the fibre-rank calculation and descent through an injective residue-field map; its
docstring and node give the complete mathematical argument.

All three modules compile together in import order without warnings using lcompile.py.

## No longer needed

No imports removed from the repository version of the item; both original public imports
are needed by its statement and retained. Removed the invalid earlier sandbox proof-only
import of `Sheaf.AlgebraicGeometry.Modules.ComplementaryBlockFiberEquality`.

The parent's direct proof dependencies `def-weil-matrix-rank`,
`def-weil-pbc-free-module`, `def-weil-sheaf-of-modules-category`, and
`lem-weil-pbc-open-immersion-module-pullback-restriction` move into the relevant genuine
subarguments, rather than being pruned from the argument. Their declarations are supplied
by existing Mathlib and WeilConjectures imports.

`lem-weil-pbc-zero-locus-eq-iff-radical-eq` is no longer needed as a separate proof
dependency: Mathlib's proved `eq_zero_of_basicOpen_eq_bot` supplies the reduced-ring
criterion directly. No separate Sheaf module for the radical/zero-locus route is imported.
The earlier uncommitted `lem-pc-complementary-block-fiber-equality` and module
`Sheaf.AlgebraicGeometry.Modules.ComplementaryBlockFiberEquality` are eliminated.

## Where the brief, the DAG or earlier work was wrong

The previous delivery split off an equivalent target; this replacement is a genuine split
between a pointwise assertion valid also on nonreduced schemes and a separately proved
reducedness criterion. The original DAG's named definitions and zero-locus equivalence did
not alone supply the fibre rank calculation or its sheaf/pullback glue. That specific step
is now an explicit next item rather than being hidden inside an equivalent restatement.

The unit route is preserved: rank vanishing in fibres, followed by reducedness, followed by
free-sheaf extensionality. No unit statement or realized step is bypassed or modified.
The source blueprint file named by the existing node is absent from this machine; the
retained parent docstring and DAG proof provide its normal-form argument. LeanSearch was
unavailable (Internal Server Error), as recorded by the required search tool; semantic
search and source grep were performed. No false statement was found.

## New nodes

`lem-pc-complementary-block-residue-vanishes`, in
`lean/Sheaf/AlgebraicGeometry/Modules/ComplementaryBlockResidueVanishes.lean`: the remaining
pointwise fibre-rank step, independent of reducedness and strictly smaller than the parent.

`lem-pc-free-map-residue-detection`, in
`lean/Sheaf/AlgebraicGeometry/Modules/FreeMapResidueDetection.lean`: a proved detection
criterion for arbitrary free source index sets and finite free targets on reduced schemes.

No change record is needed: existing interfaces and visibility are unchanged.

## Second reading by R2

1. PASS: diff against the repository shows only two plain proof imports and the
   proof replacement in the existing module. Its theorem signature, docstring,
   definitions and public imports are byte-for-byte unchanged. The existing node
   changes only proof, proof_deps and proof_origin. No change record is required.
2. PASS: all three modules compile locally in import order without warnings.
   Scratch copies with #print axioms show only propext, Classical.choice and
   Quot.sound for free_map_eq_zero_of_residue_evaluations; the parent and the
   pointwise statement additionally use sorryAx, accounted for by the single
   named pointwise hole. No definitions are added, no forbidden declarations or
   implementation attributes occur, and no arbitrary data is chosen from an
   unproved existence theorem.
3. PASS: the remaining statement is a genuinely smaller pointwise assertion,
   with no reducedness hypothesis or rank hypotheses away from its fixed point.
   Its docstring and node contain the lift, dimension, and injective residue-field
   descent argument. Checked a=0, empty complementary indices, empty U, and a
   nonreduced dual-number example (a nilpotent complementary block has zero residue
   but need not itself vanish). The proved detection theorem supports arbitrary I
   and finite J, including empty indices. Independent LeanFinder search for image
   dimensions, Loogle search for range_prodMap, and Mathlib/upstream/Sheaf grep
   found useful dimension and Schur-complement tools but no duplicate geometric
   theorem or immediate closure of the remaining pullback comparison argument.
   The private matrix-detection helper in FiniteFreeStalkUnitCancellationAt is not
   an accessible public theorem. Closing the remaining hole is not a few-minute
   application of the available API, so it is retained and explicitly reported.
4. PASS: the reduction follows pointwise rank, reduced-section detection, and
   free-sheaf extensionality; the unit's statement and realized steps are unchanged.
   The original parent public imports stay because they are part of its interface.
   The new pointwise module needs only Modules.Sheaf rather than FreeComplex;
   this smaller public import was tested successfully. All old direct proof_deps
   absent from the new parent proof are enumerated under No longer needed above;
   the zero-locus/radical lemma is replaced by proved Mathlib detection, and the
   other dependencies remain in the genuine subarguments. No existing library
   module is removed from the target closure by this delivery.
5. PASS after repair: both new nodes have the required source, proof, dependency,
   origin, search, creation, blueprint, chapter, unit and Lean records. Proof_deps
   agree with the unions of uses. The two new lean.statement strings were
   reformatted to the exact multiline Lean signatures; mathematical statements
   were not changed. The parent node records precisely its two-lemma reduction.

Second-reading changes: narrowed the new pointwise module's public import from
WeilConjectures.AlgebraicGeometry.Modules.FreeComplex to
WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf; repaired the two new
node signature records; appended this independent review. The correct proofs
were retained. One original hole is replaced by one strictly smaller hole:
this remains a decomposition, with net zero holes closed.
