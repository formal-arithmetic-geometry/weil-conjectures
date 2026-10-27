## What changed

Proved `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_affine_locally_indEtale`
in the assigned module without changing its signature. The proof transports the
ind-etale chart predicate along ULift ring isomorphisms, applies strict-local
invariance, proves exchange for sheaves in every degree by conservative geometric
stalks, and extends to all bounded-below abelian complexes with the proved
`DerivedCategory.Plus.heart_test_bounded_below`. The existing coefficient-forgetting
comparison then gives the module-valued result.

The existing stalk criterion fixes the opposite ordering of the chosen fibre product.
A proved private helper repeats that calculation for an arbitrary Cartesian square,
using the already declared canonical-model stalk localization and total-cohomology
comparisons. Other private helpers handle residue evaluation and lower bounds.
No shared module or definition was changed. The item node records this route.

The final version, including public-import cleanup, compiled with lcompile in
16.4 seconds with no warnings or errors. The preceding proof cleanup also compiled
cleanly in 20.0 seconds. The delivery tool runs the required preflight and axiom probes.
No `lake` or global build was run. The statement covers the empty schemes, zero
coefficient ring, identity base change, sheaves in degree zero, and complexes
unbounded above: the proof uses stalk conservativity, zero negative cohomology,
and the bounded-below heart test without extra assumptions.

Change record: `coord/changes/V4-ind-etale-qcqs-proof-imports.md`. There are no direct
Lean importers of the item, so no consumer adaptations are needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_affine_locally_indEtale`
(node `lem-per-ind-etale-qcqs-direct-image-base-change`).

There are zero `sorry` statements left in the item and zero holes added elsewhere;
zero split-off statements. All private helpers have complete proofs.
The proof still uses the assigned declared strict-local invariance dependency;
this is a proof from the library declarations, not a claim that all transitive
axioms have already been eliminated.

## No longer needed

Removed imports (the coefficient comparison is retained as a private import):

- `public import Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `public import Sheaf.CategoryTheory.RingedSiteModules`
- `public import WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `public import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`
- `import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`
- `import WeilConjectures.CategoryTheory.RightDerivedBaseChangeZeroUnit`
- `import WeilConjectures.AlgebraicGeometry.DerivedExchangeTermwise`
- `import Mathlib.CategoryTheory.Abelian.RightDerived`
- `import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `import Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `import Sheaf.AlgebraicGeometry.ExchangeStrictLocalCohomologyStalk`
- `import Sheaf.CategoryTheory.SiteCohomologyPullback`
- `import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`
- `import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology`

The following planned nodes cease to be proof dependencies of this item:

- `def-sp-acyclic`
- `lem-sbc-right-derived-base-change-zero-unit`
- `lem-weil-pbc-derived-exchange-termwise`
- `lem-weil-pbc-derived-functor-injective-vanishing`
- `lem-weil-pbc-dplus-injective-representative`
- `lem-weil-pbc-exchange-strict-local-cohomology-stalk-criterion`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-left-exact-injective-resolution-degree-zero`
- `lem-weil-pbc-site-cohomology-pullback`
- `src-right-derived-functor-plus-acyclic-unit`

Their acyclic-resolution, underived degree-zero and chain-map comparison route is
replaced by the already proved bounded-below heart test. The site-cohomology
pullback package is replaced by the proved cohomology invariance under an
isomorphism. The stalk-criterion module is replaced by its proved private
arbitrary-square calculation, from its existing underlying localization modules.
No upstream declaration or module is removed. These pruning claims concern this
item's dependencies; other callers may still need those modules.

The removed `tool_uses` entries are exactly the old approved entries among the
pruned node list. No tool approvals were added or reordered.

## Where the brief, the DAG or earlier work was wrong

The stated criterion uses `pullback g f` with its square flipped, whereas the item
uses `pullback f g`. Its underlying canonical-model localization theorem already
accepts an arbitrary Cartesian square, so this is an interface mismatch, not a
false statement. The private helper supplies the required square directly.

The chart hypothesis uses `IndEtaleAcrossUniverses`; strict-local invariance expects
`proAffineEtale`. A private transport proof and `proAffineEtale_iff_appTop` bridge
them without changing either definition. The original six-step argument is a valid
plan, but the proved generic heart test makes its degree-zero and acyclic-resolution
steps unnecessary. This change is below the blueprint unit level and retains the
strict-local base-change argument needed by the ancestor.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
