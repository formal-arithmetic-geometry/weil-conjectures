## What changed

Proved `AlgebraicGeometry.Etale.derivedSectionsFinitePushforwardModules` with both
public definitions and the theorem signature unchanged. The proof establishes injective
normalization and the canonical base-change mate square by derived-functor uniqueness,
composition of restriction, and adjunction identities.

Repaired every duplicate named by the return of head `4cf61d0d5f7`. Removed
`finiteSections_comp_fac`, `finiteSections_comp_unit_app`, and
`finiteSections_derived_comp_eq`. In the existing unclaimed module
`Sheaf.Paper.DerivedLerayComp`, exposed the already proved `comp_fac` and `comp_unit_app`,
and generalized `derived_comp_eq` in place to any Grothendieck abelian coefficient
category. Its original abelian-valued caller passes AddCommGrpCat explicitly; the public
`derivedLeray_comp` signature is unchanged. The item imports that module and applies all
three existing helpers. Its remaining private helpers cover the module-valued composition,
normalization and mate-square arguments. No source-library module was changed.

Updated both existing nodes to record reuse and the generalized helper attachment.
The interface change and all consumers are recorded in
`coord/changes/H6-derived-sections-reuse-comparison-helpers.md`.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Etale.derivedSectionsFinitePushforwardModules`
(node `lem-trf-derived-sections-finite-pushforward-modules`). Added zero holes and split off
zero statements. Both definitions and every private helper have complete bodies. Actual
remaining hole count in the delivery: zero. Both changed modules compiled together
through lcompile.py: DerivedLerayComp in 31 seconds and the item in 55 seconds.
The static import-pruning checks pass for both changed modules. The item retains every
original statement and definition body verbatim (checked with the delivery parser).

## No longer needed

Removed proof imports:

- `Sheaf.TraceFormula.ModuleDerivedRestrictionResolution`;
- `WeilConjectures.SixFunctors.Finite.Exact` (already publicly available through finite Leray);
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`;
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`;
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`;
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`;
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`;
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`;
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective`;
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`.

The return repair also removes the three duplicate private comparison lemmas. Their
existing counterparts in `Sheaf.Paper.DerivedLerayComp` are imported and reused.
The direct `CompConjugate` proof import from the rejected delivery is supplied by that
module instead. No module is withdrawn.

The proof no longer uses the declared dependencies
`lem-weil-pbc-module-direct-image-left-exact`,
`lem-weil-pbc-module-sheaves-colimits-forgetful`,
`lem-weil-pbc-module-sheaves-enough-injectives`,
`lem-weil-pbc-kinjective-hom-derived`,
`lem-weil-pbc-right-derived-plus-injective`,
`def-weil-pbc-constant-sheaf`,
`def-weil-sheaf-of-modules-category`, and
`lem-trf-module-derived-restriction-resolution` as proof steps. Generic module-valued finite
exactness replaces scalar forgetting. No injective resolution is chosen: the normalization
holds for every one supplied in the statement. Universal right-derived comparison equations
and mate calculus replace resolution representatives for pullback. The unchanged public
imports still expose the definitions required by the statement; this packet withdraws no
module and makes no claim that another parent's dependencies are unused.

## Where the brief, the DAG or earlier work was wrong

The proposed scalar-forgetting and comparison-of-resolutions argument is unnecessary. The
source finite-direct-image exactness theorem already accepts ModuleCat coefficients. The
normalization and pullback equation are formal consequences of the existing canonical
right-derived comparisons and adjunction identities. The bounded-below assumptions remain
in the unchanged statement, though the formal compatibility argument works unboundedly.
The unit route is preserved. The old `stmt_deps` entry for the resolution restriction
lemma is retained as required by the node-edit boundary; its proof dependency and Lean
import are removed, and it has no use in this proof.

The returned packet duplicated private helpers; importing them required exposing the
existing declarations. This repair also generalizes the existing coefficient-specific
helper in place. The change record lists the consumers and explains preservation of their
statements. No forced adaptation, source-library edit, or new node is introduced.

The rejected delivery had no reason to duplicate the two abstract categorical lemmas:
they were already coefficient-independent. The coefficient-specific `derived_comp_eq`
also admits the direct Grothendieck abelian generalization now proved in its original
Sheaf module. The repair adds no additional proper/open composition dependency.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
