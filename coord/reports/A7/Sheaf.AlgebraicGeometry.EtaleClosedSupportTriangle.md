## What changed

Proved `AlgebraicGeometry.Etale.exists_etale_closedSupportTriangle` in the assigned module,
with its complete signature and all existing public imports unchanged. The proof uses the
chosen closed adjunction, full faithfulness of derived direct images, derived open-closed
conservativity and disjoint-range vanishing. Completing the open unit and applying the
orthogonal counit-triangle theorem gives pointwise existence. Triangle morphism extension
and shift-one orthogonality prove naturality for every derived morphism.

The argument works with `[Ring A]`, including noncommutative rings, and imposes no
boundedness or constructibility. It does not use a monoidal structure on `ModuleCat A`.
The theorem docstring, inline phase comments and updated DAG describe the shorter
implemented proof.

Updated the parent node proof, proof dependencies and proof origin. Four new DAG records
attach already proved source-library declarations; no Lean declaration or obligation was
added. No definition, statement or existing declaration visibility changed, so no consumer
adaptations or change records are needed.

Validation: the single module compiles through `lcompile.py` (5–7 seconds), including after
removing a redundant explicit import of open-immersion full faithfulness. The final
`deliver3.py` dry run performs the axiom and delivery checks. Checked the mathematical edge
cases K=0, empty open, empty closed and zero coefficient ring: the same adjunction and
orthogonality argument applies. Existing public imports were retained to preserve the API.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.exists_etale_closedSupportTriangle`
(node `lem-exc-closed-support-triangle`).

Added 0 holes; split off 0 theorems. No `sorry` remains in the delivered Lean module.
The proof uses the existing supplied instance
`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`, whose
proof remains a separate existing obligation; this delivery does not claim the theorem is
independent of all existing library holes.

## No longer needed

Removed proof imports:

- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`
- `Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage`
- `Sheaf.CategoryTheory.Sites.SheafificationPlusTheorem`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
- `WeilConjectures.SixFunctors.OpenClosed.Stalk`

The replacement proof no longer directly needs these original proof-dependency nodes:

- `def-sp-injective-resolutions`
- `def-weil-abstract-derived-category`
- `def-weil-open-immersion`
- `def-weil-pbc-constant-sheaf`
- `def-weil-pbc-direct-image`
- `def-weil-pbc-etale-site`
- `def-weil-pbc-inverse-image`
- `def-weil-presheaf-modules-sheafification`
- `def-weil-sheaf-of-modules-category`
- `def-weil-size-convention`
- `lem-kun-04ca`
- `lem-pur-kinjective-degreewise-existence`
- `lem-pur-kinjective-restrict-localized`
- `lem-pur-ring-presheaf-sheafification-localization`
- `lem-weil-pbc-cochain-complexes-degreewise-exact`
- `lem-weil-pbc-complex-ses-triangle`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `lem-weil-pbc-etale-site-localization-open`
- `lem-weil-pbc-exact-functor-complex-cohomology`
- `lem-weil-pbc-free-yoneda-presheaf-module`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-open-immersion-base-change`
- `lem-weil-pbc-open-immersion-etale`
- `lem-weil-pbc-ring-sheafification-underlying-sets`
- `lem-weil-pbc-ring-sheaves-grothendieck`
- `lem-weil-pbc-ringed-site-module-sheafification-exact`
- `lem-weil-pbc-site-restriction-exact`
- `lem-weil-pbc-site-sheafification-sections-local`
- `lem-weil-pbc-termwise-adjunction-homotopy`
- `lemma-openclosed-stalk-lowerstar`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `prop-weil-pbc-geometric-stalks-exact`

The discarded construction of an injective-term support short exact sequence is replaced
by formal adjunction and triangle calculus. The closed-ambient adjoint itself remains in
the proof. Some discarded nodes may still be needed transitively by it or other parents;
this report claims removal of the assigned item's direct proof dependency, not global
unreachability. The original public imports RingedSiteModules, KInjectiveTotalDerived and
ConstantSheaf remain to preserve what existing importers see.

Pruned obsolete `tool_uses` approvals (the remaining approvals retain their original order):

- `lem-kun-04ca`
- `lem-pur-kinjective-degreewise-existence`
- `lem-pur-kinjective-restrict-localized`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `lem-weil-pbc-etale-site-localization-open`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-ring-sheaves-grothendieck`
- `lem-weil-pbc-sheafification-plus-theorem`
- `lem-weil-pbc-site-restriction-exact`
- `lem-weil-pbc-site-sheafification-sections-local`
- `lem-weil-pbc-termwise-adjunction-homotopy`
- `lemma-openclosed-stalk-lowerstar`
- `lemma-weil-pbc-geometric-stalk-conservative`

## Where the brief, the DAG or earlier work was wrong

The original direct-resolution plan is mathematically reasonable but unnecessary given
already proved source-library results. The search history's old zero-hit results missed
`WeilConjectures.SixFunctors.OpenClosed.Derived` and the orthogonal-counit theorem in
`WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated`.

The generic open-closed triangle in `OpenClosed.Derived` has monoidal coefficient hypotheses,
so it cannot simply be specialized to a possibly noncommutative ring. Its conservativity
and vanishing results have no such hypotheses; those are the only results taken from it.
Closed and open direct-image full faithfulness lifts through the source library's
K-injective fully-faithful right-derived theorem. No unit statement or realized unit step
is bypassed (`sk-prop-sf-existence.realized` contains no node bound to this proof route).

The four newly recorded declarations are already proved tools; their attachments do not
create any new work. No false-statement repair was necessary.

## New nodes

`lem-exc-kinjective-derived-fully-faithful` records the existing
`Functor.full_rightDerivedFunctor` and `Functor.faithful_rightDerivedFunctor` in the source
library. Its proof computes morphisms between K-injectives and transports to all objects.

`lem-exc-derived-open-closed-conservative` records the existing arbitrary-coefficient
`jointlyReflectIsomorphisms_mapDerivedCategoryUpperStar'`. Its source proves the underlying
sheaf result by the supported-sheaf comparison, then lifts joint conservativity through
homology.

`lem-exc-derived-open-closed-vanishing` records the existing
`isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar_of_disjoint_range`. It computes
on K-injective representatives and applies sheaf-level disjoint-range vanishing termwise.

`lem-exc-orthogonal-counit-triangle` records the existing
`exists_distTriang_counit_of_subsingleton`. Its Hom-exactness proof identifies the first
vertex of a distinguished triangle with the source of the adjunction counit.

All four records have `lean.existing: true`, no new module, complete proofs in words,
source references and logged three-kind searches. No new holes or data choices were added.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
