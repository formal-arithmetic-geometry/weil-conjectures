## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.GaloisCover.exists_stalk_normalization_formal_split`
with a proof using the existing `iso_of_finite_depth_two_extensions` theorem.
The two new modules separate its remaining geometric inputs: source boundary depths
and splitting over the punctured formal test. The original signature and docstring
are unchanged. Proof-only imports provide the Noetherian power-series instance and
finiteness of the split coproduct projection. The existing node now records this route.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.GaloisCover.exists_stalk_normalization_formal_split`.
No `sorry` remains in the assigned module. Added exactly two holes:

- `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_formal_boundary_depths`
  (node `lem-sbc-stalk-normalization-formal-boundary-depths`). It asserts only the two
  boundary depth bounds, with no section, generic fibre, or torsor assumptions.
- `AlgebraicGeometry.Scheme.GaloisCover.exists_stalk_normalization_formal_punctured_split`
  (node `lem-sbc-stalk-normalization-formal-punctured-split`). It asserts an isomorphism
  over the punctured open, with its equation over that open, and makes no assertion
  over the entire test.

This is a decomposition, not a net decrease in holes: one closed, two added.
All three modules compile through `lcompile.py --all`. The proof combines the two
inputs by the already proved depth-two uniqueness theorem. The trivial group and
zero-variable cases are included. No new data definitions or arbitrary witnesses
are introduced, and no existing declaration's signature or visibility changes.

## No longer needed

Removed these direct proof imports from the assigned module and relocated them to
exactly the intermediate module that needs them:

- `Sheaf.AlgebraicGeometry.Morphisms.GenericFibreActionExtension`
- `Sheaf.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull`
- `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationNormalDense`
- `Sheaf.RingTheory.FlatLocalDepthFormula`
- `Sheaf.RingTheory.NormalLocalDepthTwo`
- `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedSectionFullyFaithful`

Their corresponding original proof-dependency nodes remain needed transitively:
`lem-sbc-generic-fibre-action-extension`, `lem-sbc-normal-integral-generic-hom-full`,
`lem-sbc-stalk-normalization-normal-dense`, `lem-weil-pbc-flat-local-depth-formula`,
`lem-weil-pbc-normal-local-depth-two`, and
`lem-sbc-power-series-punctured-section-fully-faithful`.
Second reading also removed unused direct public imports from the new boundary-depth module:
`Mathlib.AlgebraicGeometry.FunctionField`,
`Mathlib.AlgebraicGeometry.Geometrically.Connected`, and
`WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor`.
These modules remain available elsewhere in the import closure.
No node or module is pruned from the target closure. The unit's final local
calculation and depth-two uniqueness route remain intact.

## Where the brief, the DAG or earlier work was wrong

The original dependencies provide normality, generic action extension, full
faithfulness, and depth formulas separately, but do not provide the comparison
maps or the local boundary-depth assembly for this concrete normalization.
Those are the two remaining geometric interfaces now explicitly recorded.
The target statement itself was not disputed or changed. During development an
isomorphism/projection-equation split was rejected because an arbitrary scheme
isomorphism need not commute with the projection; no such declaration remains
in the delivery. The delivered intermediate conclusions are strict parts of the
original argument, and the uniqueness application is a real Lean proof.

## New nodes

`lem-sbc-stalk-normalization-formal-boundary-depths` is in
`dag/nodes/sec-smooth-base-change/lem-sbc-stalk-normalization-formal-boundary-depths.json`
and is stated by `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalBoundaryDepths`.
Its proof follows normal Serre S2, going down, and flat local depth in the local
normalization argument of Stacks 0EYJ, 0337 and 031S.

`lem-sbc-stalk-normalization-formal-punctured-split` is in
`dag/nodes/sec-smooth-base-change/lem-sbc-stalk-normalization-formal-punctured-split.json`
and is stated by `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalPuncturedSplit`.
Its proof follows the rational section point, generic full faithfulness, and
power-series full faithfulness calculation of Stacks 0EYJ and 0EY9.

## Second reading by S4

1. Compared the assigned module with the repository by diff and checked the existing
   theorem signature byte for byte: unchanged. The original docstring and visibility
   are unchanged. The other two delivered Lean modules are new. There are no definition
   changes, interface adaptations, or change records.
2. Compiled all three modules through lcompile.py. Only the two named and reported new
   theorems contain sorry; no definition, axiom, unsafe, opaque, implemented_by, or extern
   was added. The main proof applies the two geometric inputs with their displayed
   projection equation to iso_of_finite_depth_two_extensions, in the correct orientation.
   The scratch axiom checks show only propext, Classical.choice, Quot.sound, and sorryAx
   (the two open geometric inputs). This is a decomposition: one original hole closed,
   two strictly smaller holes added, net minus one; no claim of a completed theorem.
3. Read the two complete natural-language proof docstrings and their DAG nodes against
   Stacks 0EYJ, 0EY9 and 0EY6. The boundary lemma needs no torsor: normality, going down,
   normal S2, and flat local depth give its two bounds. The punctured lemma uses generic
   splitting on the normal punctured section followed by power-series full faithfulness,
   retaining the equation over V; it makes no boundary assertion. Checked zero variables
   (identity slice), the trivial group (one summand), and an empty PA in the boundary
   lemma (the normalization source is empty, its depth bound vacuous). Searched with new
   LeanFinder/Loogle/grep queries and rg in Sheaf and the upstream source. Going-down,
   finite coproduct, generic-fullness and power-series coefficient-model results are
   components, not exact replacements; the upper normalization splitting declarations
   already depend on this item and cannot be used here. Neither new statement is a
   restatement of the whole item. No short proof closing either new hole was found.
4. The reduction uses the existing uniqueness theorem and relocates all six original
   proof-dependency modules to their appropriate geometric input. The report lists all
   six and their nodes; none is pruned transitively. All proof-only imports are plain
   imports. Removed three unused public imports from the new boundary-depth module;
   it still compiles. The route retains the unit's punctured-slice calculation and
   depth-two extension. The repository's sk-prop-input-spreading realized arrays were
   already empty; this delivery does not modify that unit record or bypass its steps.
5. Checked each node's verbatim lean.statement against its module and checked that
   proof_deps is the union of the proof steps' uses. The existing node's changed proof,
   dependencies and origin describe the actual final uniqueness application. Each new
   node has its source, searches, creation record, blueprint, chapter, unit, and Lean
   record. Verdict: a valid decomposition, with the two geometric holes explicit.

Removed the new boundary-depth module's three unused public imports, added the
proof-only Mathlib going-down import, and repaired its DAG plan to cite the existing
Mathlib-matched node lem-weil-pbc-going-down-normal-integral for that non-elementary
step. Added the independent search results to the new nodes and expanded this report. No mathematical
statement or proof body was changed during the second reading.
