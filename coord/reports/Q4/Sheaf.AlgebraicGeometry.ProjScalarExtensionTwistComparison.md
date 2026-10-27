## What changed

Replaced the hole in `AlgebraicGeometry.Proj.scalarExtension_twist_comparison` by a Lean
assembly from three strictly smaller assertions: existence of the normalized isomorphisms;
uniqueness/product/unit/identity fraction laws for already given isomorphisms; and the
composition equation for already given normalized comparisons and a proved equality of
scheme maps. The original theorem statement is unchanged.

Two substantial calculations are proved directly, with no added assumptions:

- The homogeneous-section formula specializes the existing fraction predicate to denominator
  one. The proof supplies the source fraction identity with `val_unitToTwist_app_apply`, then
  uses pointwise extensionality and the actual restriction map.
- The coefficient equivalence for R→S→T is explicitly constructed using
  `Algebra.TensorProduct.cancelBaseChange`, tensor congruence and the supplied beta and gamma.
  Its formula is proved on pure tensors. Induction on the degreewise S-spans, using the
  semilinearity derived from gamma, proves the composite degreewise T-span assertion.

The equality `p = q ≫ r` is also proved directly. The span conditions imply the requisite
irrelevant-ideal inequalities. Standard affine cover extensionality identifies each scheme
map with the canonical `Proj.map`; `Proj.map_comp` then gives the equality. The remaining
composition obligation assumes this already proved equality and concerns only the twist maps.

Moved the existing `scalarExtensionTwistSection` and `IsScalarExtensionTwistComparison`
definitions, with their original bodies, signatures, visibility and docstrings, into
`Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistData`. The item publicly imports this data
module and retains all five original public imports. This avoids an import cycle when the
three new assertion modules use the normalization definitions. No source-library file or
existing module other than the assigned item is changed.

The change record is `coord/changes/proj-scalar-extension-twist-data-relocation.md`.
An exact importer search and `tools/downstream.py` both report no current direct or indirect
Lean importers of the item, and no users of the moved names outside the item. No consumer
adaptation is required. The item remains needed by its DAG parents and is not withdrawn.

Validation: all five delivered Lean modules have compiled through `lcompile.py`, with the
three obligation modules reporting their single expected `sorry` warning. The final assigned
module compiles in 7.4 seconds. Its theorem signature and the two relocated definition bodies
were checked against the shared originals; they are unchanged. All Lean lines are at most
100 characters.

## Proved and sorry left

One original hole is closed **by decomposition**, not by a complete proof from standard axioms:

- `AlgebraicGeometry.Proj.scalarExtension_twist_comparison`
  (`lem-sfb-proj-scalar-extension-twist-comparison`).

Three new holes remain, one whole named theorem in each new module:

- `AlgebraicGeometry.Proj.scalarExtension_twist_exists`
  (`lem-sfb-proj-scalar-extension-twist-existence`).
- `AlgebraicGeometry.Proj.scalarExtension_twist_fraction_laws`
  (`lem-sfb-proj-scalar-extension-twist-fraction-laws`).
- `AlgebraicGeometry.Proj.scalarExtension_twist_composition_law`
  (`lem-sfb-proj-scalar-extension-twist-composition-law`).

There are no holes in the data module, the assigned module, or any private helper.
Direct holes change from one to three: one upper hole closed, three lower holes added,
net minus two. Each remaining statement has its own source, complete proof in words and
DAG node. None is the original assertion under another name: the existence assertion omits
all coherence conclusions, the fraction-law assertion constructs no isomorphism, and the
composition assertion assumes the scheme-map equality and constructs no coefficient or
twist equivalence. In particular the homogeneous-section, coefficient-composition and
scheme-composition clauses are supplied by actual proofs, not repackaged assumptions.

## No longer needed

No mathematical node or module is globally pruned or withdrawn. The old six-step route is
preserved among the three new obligations and the direct calculations in the parent.

The following original private proof imports are removed from the item and retained where
the corresponding construction or law remains to be proved:

- `Sheaf.RingTheory.HomogeneousLocalizationScalarExtension`
- `Sheaf.Algebra.Module.GradedLocalizationScalarExtension`
- `Mathlib.AlgebraicGeometry.Modules.Tilde`
- `WeilConjectures.Topology.GlueSheavesOfModules`
- `WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
- `WeilConjectures.AlgebraicGeometry.ModulePullbackTensor`
- `WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists`
- `WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`

These are dependencies moved into the lower obligations, not eliminated work. The parent
now imports those three assertions privately and Mathlib's tensor-map API for its explicit
coefficient calculation and Proj functoriality for its scheme-map calculation. All original public imports remain. The old tool approvals remain
valid for the construction route in the children; no new approval is invented.

## Where the brief, the DAG or earlier work was wrong

No false statement or target correction was needed. The item currently has one hole and
is a proof assignment, not a zero-hole repair. No current rework row or build-error file
is present in the shared snapshot.

The planned gluing and affine localization declarations are available, but they do not
already package the chartwise arbitrary-twist isomorphism with the pointwise fraction
predicate used here. The three new obligations make those unformalized steps explicit.
`GradedProjQuotientTwistComparison` was also inspected: its surjectivity and degree-one
generation assumptions do not apply to the arbitrary scalar extensions here, so its
comparison theorem does not supply a shorter route.
The original blueprint unit has empty realized arrays, and its mathematical route is
preserved: no unit statement or proof step is bypassed.

Edge cases checked in the mathematical reduction include empty Proj and empty opens,
zero coefficient rings, nilpotent or killed chart denominators, arbitrary integer twists,
and nonflat scalar extensions. The direct proofs cancel no element of an original ring,
and require neither degree-one generation nor invertibility of a twist.

The overlaid DAG has exactly the two pre-existing cycles in the base snapshot, both in
`lem-nagata-affine-proj-scalar-extension` and relative-Proj functoriality/existence.
The packet creates no additional dependency cycle. This is reported for the maintainer;
those nodes are outside this assignment and have not been edited.

## New nodes

- `def-sfb-proj-scalar-extension-twist-normalization` records the two relocated, unchanged
  definitions in `ProjScalarExtensionTwistData`; it adds no construction or hole.
- `lem-sfb-proj-scalar-extension-twist-existence` is precisely the chart equivalence,
  compatibility and gluing construction of original steps 1–4, before any coherence law.
- `lem-sfb-proj-scalar-extension-twist-fraction-laws` isolates the generator/faithfulness
  proof of uniqueness, the original multiplication/unit calculation, and identity
  normalization. It asserts properties only of already given normalized comparisons.
- `lem-sfb-proj-scalar-extension-twist-composition-law` isolates equality of the twist maps
  after the coefficient construction and scheme-map composition equality have been proved.

All node files are under `dag/nodes/sec-six-functors-basics/`, with the original unit and
source. `blueprint_refs.py ancestor` reports no imported blueprint ancestor for the item;
the new nodes preserve that null ancestor, its detailed origin and its via chain.
The blueprint search found no matching existing scalar-extension twist comparison node. Mathlib grep, Loogle and LeanFinder searches found chart
intersection results, but no existing arbitrary-twist normalized comparison theorem.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistComparison": "b5a123a2f140b7f1f2f0298259ab97e4e6c9edb3", "Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistCompositionLaw": "98e76d2b14d3777d52fa34af91311b23f83577ca", "Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistData": "4ed08f8a7fe69b3a773f48a66218088fdc2b6042", "Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistExistence": "a1ba76c59a6897a64cc3b8403cb56c35f83b9307", "Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistFractionLaws": "724ada70f76a7745122747cd46773cfc7e5d3074"}, "results": {}, "time": "2026-10-27T23:54:06+0800", "transitive": 0, "version": 1}
```

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
