## What changed

Completed `AlgebraicGeometry.Etale.sfEtaleUnitTensorArbitraryBase`, preserving its statement
and all three public helper definitions. Private proved categorical calculations establish the
conjugate/Hom-equivalence formula, the adjunct of a tensor projection, and transport of the
left-unit law along the exact/left-derived pullback comparison. The graph/projection square
then gives the actual tensor-normalization equation. Invertibility follows by cancellation.
No geometric finiteness, boundedness or nonzero-coefficient hypothesis is added.

Extracted the existing `supportDerivedTensorIso` and `supportExactPullbackTensorIso` into
`Sheaf.AlgebraicGeometry.ExactPullbackTensorComparison`, preserving names, signatures and
bodies. `SupportedLocalizationComparisons` publicly re-exports them. Both the graph module and
its current `SfEtaleGraphUnitTensor` proof dependency change only their public import of that
old module to the new foundational module. This is required
to remove a source import cycle through smooth duality. No source-library module is edited.
Change record: `coord/changes/R6-exact-pullback-tensor-foundation.md`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.sfEtaleUnitTensorArbitraryBase`
(node `lem-sf-etale-unit-tensor-arbitrary-base`). The item has zero remaining holes.
Added zero holes; split off zero proof statements. The new definition module, the adapted
support module and the current graph module have zero holes. G9's landed graph theorem
proof is preserved verbatim. The newly adapted dependency retains its single existing hole:
`AlgebraicGeometry.Etale.sfEtaleGraphUnitTensor`
(node `lem-sf-etale-graph-unit-tensor`). Thus the packet contains one unchanged dependency
hole and closes the item's original hole without adding another.

## No longer needed

Removed these unused private imports from the item:

- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Sheaf.CategoryTheory.UnitAdjunctTensorAction`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationIso`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`

The item no longer directly uses the following planned dependencies. Their obsolete
`tool_uses` entries are removed where present, preserving the order of retained approvals:

- `lem-weil-pbc-etale-restriction-injectives`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-termwise-adjunction-homotopy`
- `lem-weil-pbc-exact-functor-derived-factorization`
- `lem-weil-pbc-localization-universal-property`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-sfb-ringed-derived-monoidal-comparisons`
- `lem-pur-unit-adjunct-tensor-action`

The exact sum/evaluation adjunction and canonical monoidal tensor/unit laws already exist
as specific proved library declarations. The generic arbitrary ringed-topos monoidal system
and generic unit-adjunct action theorem are unnecessary: the short private calculations
use the existing exact adjunction, projectionMap API, conjugateEquiv API, and the proved
upstream `leftDerivedUpperStarTensorComparison_leftUnitor_hom` directly. The remaining
planned localization and injective theory is already encapsulated by the exact derived
adjunction. These dependencies may remain needed by other nodes or by the graph proof;
this delivery withdraws no modules or declarations and does not claim whole-project pruning.

The graph module and `SfEtaleGraphUnitTensor` no longer directly import
`SupportedLocalizationComparisons`; they need only the relocated canonical tensor definitions
from `ExactPullbackTensorComparison`. All other imports and declarations in both current
files are preserved verbatim. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The source dependency attached to the graph statement prevented using that statement from
its intended parent: graph → SupportedLocalizationComparisons → NormalizedSupportTriangle
→ SupportedExteriorProduct → upstream Kunneth.Defs → Stability → SmoothDuality → this item.
The current graph-unit dependency has the same path through the support module. This was an import organization problem, not a false theorem.
The foundational extraction fixes it without changing any mathematical object. The unit route
is preserved: this node is not itself a unit-realized declaration, its parent remains in place,
and the graph/projection step is still used.

The planned generic strong-monoidal-system and unit-adjunct infrastructure was more general
than this calculation needs. The concrete upstream tensor comparison and its left-unit law
supply precisely the required canonical maps. Empty source, identity morphisms, arbitrary
non-quasi-compact opens and A = 0 retain their original types and no new assumptions.

The return of delivery `7f04de25d` identified an overlapping landing in the graph module.
This repair takes the complete current graph source and graph DAG record from landing
`678933a79e6`, retaining G9's new private lemmas, complete theorem proof, reduced imports
and new graph-unit dependency. The sole graph source edit is the tensor-foundation import
replacement. The same import in the newly landed graph-unit dependency must also change:
restoring either original import in the source overlay closes a path back to this item.
The import-only adaptations were checked byte for byte against current sources.

## Forced adaptations

Both `Sheaf.AlgebraicGeometry.SfEtaleGraphProjectionArbitraryBase` and
`Sheaf.AlgebraicGeometry.SfEtaleGraphUnitTensor` are currently unclaimed (G9 delivered them).
Each original import of `SupportedLocalizationComparisons` closes the source cycle through
`NormalizedSupportTriangle`, `SupportedExteriorProduct`, upstream `Kunneth.Defs`, `Stability`,
`SmoothDuality` and this item. The graph module additionally imports the graph-unit module,
so changing only the graph import no longer breaks all cycles after G9's landing.
For each file, restoring its old import in the otherwise delivered overlay reproduces the
path to this item; with both replacements neither reaches this item. This is an import-graph
failure before tactic/type checking. Each file changes exactly one line:
`public import Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons` becomes
`public import Sheaf.AlgebraicGeometry.ExactPullbackTensorComparison`.
Every current signature, visibility, docstring and proof body is preserved. The support
module remains unclaimed; its edits only relocate and re-export the two unchanged definitions.

## New nodes

`def-sf-exact-pullback-tensor-comparison` owns the two relocated real constructions in
`Sheaf.AlgebraicGeometry.ExactPullbackTensorComparison`. This is an ownership/extraction node,
not a new proof obligation or a duplicate definition. Its source and canonical construction
are unchanged from `def-pur-supported-localization-comparisons`; that node's declaration list
now names only the declarations physically left in its old module. The new node is used by
the item's tensor-transport proof. The graph node's Lean note records its changed import owner.
Change record: `coord/changes/R6-exact-pullback-tensor-foundation.md`.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
