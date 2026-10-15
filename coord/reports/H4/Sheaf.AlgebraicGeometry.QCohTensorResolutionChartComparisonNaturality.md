## What changed

Proved `AlgebraicGeometry.tensorResolutionChartComparisonIso_naturality` with its
original statement. The proof uses augmentation naturality, the three compatible
restriction squares, the common K-flat homology comparison, normalized restriction
naturality, and categorical inverse cancellation. Added proof imports of
`QCohTensorResolutionChartAugmentationNaturality`,
`QCohTensorResolutionComparisonRestrictionNaturality`, and the new single-chart formula API
`QCohTensorResolutionChartComparisonIsoFormula`.

The comparison definition uses the four tensor maps directly, is protected from
implicit unfolding, and has a proved hom equation. The new
`QCohTensorResolutionComparisonRestrictionNaturality` module provides the proved
restriction naturality API. The existing `QCohTensorResolutionComparisonNaturality`
module is unchanged. The hom equation lives in the new
`QCohTensorResolutionComparisonFormula` module; the bundled-ring K-flatness theorem
lives in the new `QCohTensorResolutionKFlatBundledRing` module.
All existing signatures and mathematical constructions are unchanged up to
definitional equality. The single-chart identification, left open in the previous
attempt, is now proved by reflexivity.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.tensorResolutionChartComparisonIso_naturality`
(`new-t3-qcoh-tensor-resolution-chart-comparison-naturality`).

Also proved the four new API theorems:

- `AlgebraicGeometry.tensorResolutionComparison_hom`
  (`new-h4-qcoh-tensor-comparison-hom-formula`);
- `AlgebraicGeometry.tensorResolutionComparison_restriction`
  (`new-h4-qcoh-tensor-comparison-restriction-naturality`);
- `AlgebraicGeometry.tensorResolution_isKFlat_bundledRing`
  (`new-h4-qcoh-kflat-bundled-ring`);
- `AlgebraicGeometry.tensorResolutionChartComparisonIso_hom_eq`
  (`new-h4-qcoh-chart-comparison-hom-identification`).

No `sorry` remains in any delivered Lean file. No holes are added: one original
hole closed, zero split off. Explicit axiom checks of the target, the four new API
theorems, both comparison definitions and the categorical zigzag theorem show
only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed

Removed these redundant direct proof imports from the item:

- `Sheaf.Algebra.Homology.KFlat`;
- `Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction`;
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`;
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`.

Their declarations remain available through the comparison and chart APIs and
are still used transitively; no mathematical node or module is claimed pruned.
The original four-square route and blueprint unit route are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the statement or plan was found. The local clone does
not contain the unit's referenced literature `_section.md`; the unit JSON contains
its full statement, proof step and realization record, which were read instead.
The first delivery
placed three new public statements in existing modules; the second reader moved
each into its own module, as required by the brief, and updated the imports and
node attachments. The bundled-ring node now explicitly records the bounded-flat
and affine-tilde mathematical dependencies of the theorem it reuses. The existing
comparison
and component restriction definitions needed an explicit equation API to avoid
unfolding nested tensor totalizations during conversion. The direct four-map
construction is definitionally the previous construction. The named chart
transition allows the checker to reuse its complex type. The earlier attempt's
single-chart split is unnecessary as an open obligation: its equation is proved
by reflexivity with the bundled section ring kept intact.

## New nodes

`new-h4-qcoh-tensor-comparison-hom-formula` records the proved defining equation of
the comparison in `QCohTensorResolutionComparisonFormula`. Its proof is reflexivity and adds no mathematical hypothesis.

`new-h4-qcoh-tensor-comparison-restriction-naturality` records the proved generic
restriction square before normalization, in
`QCohTensorResolutionComparisonRestrictionNaturality`. Its proof uses the four tensor squares,
the homology zigzag, and the defining equation.

`new-h4-qcoh-kflat-bundled-ring` records the proved bundling conversion of the
affine K-flatness theorem, in `QCohTensorResolutionKFlatBundledRing`, used to avoid rebuilding Spec from the section ring's
carrier.

`new-h4-qcoh-chart-comparison-hom-identification` records the proved single-chart
identification, in `QCohTensorResolutionChartComparisonIsoFormula`. The proof is
reflexivity; this node leaves no work for a subsequent session.

Change records: `coord/changes/H4-qcoh-tensor-comparison-api.md` and
`coord/changes/H4-qcoh-chart-comparison-kflat.md`. No module held by another group
is adapted, and no signature change forces an adaptation.


## Second reading by H4

1. **Interfaces: pass.** Compared all delivered existing modules with the repository
   versions, including raw signature substrings: every existing declaration's
   signature is byte for byte unchanged. The only construction edits are the
   four tensor-map presentation and proof certificates documented in the two
   change records. A scratch copy of the old comparison, with both definitions
   explicitly unfolded, equals the new comparison by `rfl`. The new irreducibility
   attribute controls elaboration; it does not alter the construction. The two
   records list all existing textual users found by `tools/downstream.py --uses`.
   No module held by another group is adapted, and no target meaning changes.

2. **Proofs: pass.** Compiled each delivered module with `lcompile.py`. Searched
   delivered sources for forbidden mechanisms and holes: none. Explicit
   `#print axioms` checks of the target, all four new API theorems, the two
   comparison definitions and the zigzag theorem show exactly the three permitted
   axioms and no `sorryAx`. The private chart-transition definition is an explicit
   composition of the existing extension and sheafification constructions.
   Inverses are taken only for maps proved invertible; no arbitrary witness is
   chosen from an unproved existence theorem.

3. **New statements: pass.** All four new API statements are proved; no statement
   is split off with a hole. Matched each verbatim Lean statement to its node and
   read its word proof. The generic restriction theorem supplies only the
   unnormalized comparison square; the target still proves the chart and
   normalization steps. Checked degree zero, identical charts, zero complexes,
   zero vertical maps and the zero ring: the proof requires no extra assumptions
   in these cases. New leanfinder, loogle and grep searches for exact-functor
   homology naturality found `ShortComplex.mapHomologyIso_inv_naturality` and its
   variants, already used by the existing homology-square API. Reading the
   surrounding library found no shorter replacement for the chart argument.

4. **Route and pruning: pass.** Read the proof from the target downward. It uses
   augmentation naturality, the two restriction-naturality squares, the four
   tensor squares through the fixed F, homology zigzag cancellation, then inverse
   normalized restriction. The original four proof dependencies are retained
   through these APIs; none is silently discarded. The four redundant direct
   proof imports are listed above. No mathematical module is claimed pruned, and
   no unit realization or route is changed.

5. **Nodes: pass after repair.** The existing node changes only `proof`,
   `proof_deps` and `proof_origin`; its statement and attachment are unchanged.
   The four new nodes have their required source, creation, search, blueprint
   and Lean records. Their proof-dependency lists equal the union of their
   proof-step uses. Updated three module attachments after moving the lemmas,
   and recorded the bounded-flat and affine-tilde dependencies underlying the
   bundled-ring wrapper. The new statements explicitly cite their definition
   dependencies.

Second-reading changes: moved three new public lemmas into their own modules
(`QCohTensorResolutionComparisonFormula`,
`QCohTensorResolutionComparisonRestrictionNaturality`, and
`QCohTensorResolutionKFlatBundledRing`), restored the existing
`QCohTensorResolutionComparisonNaturality` module by omitting it from the delivery,
updated imports, node attachments and dependency citations, and change records,
made the formula proof explicitly
unfold its protected definition, gave the moved local instances distinct names,
and fixed whitespace and a long line. The public import of the bundled-ring
module is required by the exposed comparison definition; imports used only by
theorem proofs are plain imports. The mathematical argument is unchanged.
