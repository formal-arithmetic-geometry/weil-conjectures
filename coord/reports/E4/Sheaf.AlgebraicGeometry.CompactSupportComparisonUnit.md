## What changed

Completed `AlgebraicGeometry.ProEtale.isIso_compactSupportComparisonUnit` in
`Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`. The proof specializes the
existing comparison adjunction to `ModuleCat Λ`, uses the ordinary unit isomorphism
and comparison injective acyclicity, and applies the proved generic theorem
`Adjunction.isIso_derivedPlus_unit_app_of_rightAcyclic`. The equality
`Adjunction.derivedAdjunctionPlus_eq_derivedPlus` identifies its adjunction with the
specified canonical adjunction. `NatTrans.isIso_iff_isIso_app` assembles the result.
The definition `compactSupportComparisonUnit` remains unchanged, as `asIso` of
exactly that unit. No declaration signature changed and no new definition was made.

Read Stacks `proetale.tex`, lemma-relative-comparison (099V), especially its second
proof paragraph: choose bounded-below injectives, apply inverse image, compute
right derived direct image by acyclic terms, and use the ordinary unit. The generic
criterion is the already formalized version of this very argument, not a different
geometric route. The unit's statement and all chapter/unit steps are retained.

Removed the unused public import of
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`. Its realized-coefficient
adjunction definitions are used in the existing signature of
`Sheaf.Paper.PurityComparisonUnitInjectiveModel`, so that consumer now imports the
module directly. This is the sole consumer adaptation and changes no declaration.
The node copy records the actual shorter implementation through existing generic
and finite-level declarations. Change record:
`coord/changes/compact-support-comparison-unit-imports.md`.

Validation: the item and all eleven direct consumers compile cleanly through
`lcompile.py` (two batches; at most 44.1 seconds per file). Consumer checks use the
compiled item overlay, not the published version. The original injective-model
consumer fails with unknown identifiers `finiteCoefficientDirectImage`,
`finiteCoefficientDerivedComparisonAdjunction`, and
`finiteCoefficientComparisonAdjunction`; the added direct import supplies them.
The ordinary unit, acyclicity, derived criterion, and adjunction equality were all
read in their defining modules. Mathlib searches used leanfinder, loogle, and grep;
none replaces this existing source-library criterion. The original and new
statements apply to every scheme, including the empty scheme, and to every finite
commutative ring including the zero ring; no new hypotheses were introduced.

## Proved and sorry left

Closed one of one holes in the item:
`AlgebraicGeometry.ProEtale.isIso_compactSupportComparisonUnit`
(node `thm-weil-pbc-site-comparison`). The item now has zero holes.

Added zero holes and split off zero statements. The adapted module's existing hole
`AlgebraicGeometry.ProEtale.comparisonUnitInjectiveModel`
(node `lem-pur-comparison-unit-injective-model`) is untouched. This delivery proves
its assigned item from existing declarations; the existing transitive comparison
acyclicity dependencies remain subject to their own proof obligations.

## No longer needed

Removed import: `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived` from the
item. In particular its separate `siteComparison_boundedBelow` hole is not used by
the fixed-module unit proof. This is a removed dependency of this module, not a
claim that the realized-coefficient module disappears from the whole project: the
injective-model consumer still needs its adjunction definitions explicitly.

The following former direct proof dependencies are absorbed by the proved generic
criterion or by the existing finite-level source theorems, and are not separately
imported or reproved here:

- `def-weil-pbc-proetale-modules` (the fixed ModuleCat encoding is already specified).
- `def-weil-sheaf-of-modules-category` (existing abelian and Grothendieck instances).
- `prop-weil-pbc-site-comparison-finite-level`, module
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel` (use its exact existing
  source-library unit and injective-acyclicity declarations directly).
- `lem-weil-pbc-exact-functor-bounded-below` (existing exact-functor construction).
- `lem-sc-bounded-below-injective-resolution`, module
  `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution`.
- `lem-weil-pbc-right-derived-plus-injective`.
- `lem-weil-pbc-right-adjoint-preserves-kinjective`.
- `lem-weil-pbc-kinjective-hom-derived`.
- `lem-weil-pbc-termwise-adjunction-homotopy`.
- `lemma-weil-pbc-leray-acyclicity`.
- `lem-weil-pbc-leray-acyclicity-quasi-iso`.

The last seven generic homological statements and the injective resolution are
already incorporated in the proved source-library criterion and its prerequisites;
no corresponding separate Sheaf proof-dependency module is needed by this item.
Obsolete top-level tool approvals for the former explicit generic steps are removed.
The replacement generic node `lem-cbc-derived-unit-injective-acyclicity` already
records the proved source theorem; no new node or new obligation is created.

## Where the brief, the DAG or earlier work was wrong

The previous plan was mathematically sound but did not exploit the existing proved
`PlusAdjunctionAcyclic` criterion. It described each step separately despite the
source library already implementing that same injective-resolution argument. The
realized-coefficient theorem is unnecessary for the fixed-module statement.

One previous consumer relied on the item's reexport of a module defining other
adjunctions. Its direct import is now explicit. No mathematical statement was found
false; no target statement or definition was changed. There is no delegation or
second-reader claim in this report; the maintainer's independent review remains.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
