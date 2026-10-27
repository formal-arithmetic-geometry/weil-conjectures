## What changed

Filled `AlgebraicGeometry.ProEtale.finiteSiteWordRefinement`, including all ten conjuncts.
The proof uses the existing exact-functor lower-bound theorem, qcqs proper-map instances,
canonical direct-image composition and unit equations, and the published open comparison.
The two compositor normalizations are checked through their adjunction unit equations.
Private proved localization helpers transport the open composition and identity laws.
The returned duplicate-statement findings are repaired by making their category binders
explicit: each category has an independent object universe and morphism universe.
The final pushed-refinement equation follows by direct-image composition, naturality,
and expansion of the specified pro-etale refinement isomorphism.

All seven original definition bodies, the main theorem statement and existing docstrings
are unchanged. Added the private proof import `Sheaf.CategoryTheory.DerivedExactSquare`.
Removed unused proof imports listed below. No other library module is changed.
Updated `lem-sp-finite-site-word-refinement` to record the actual dependency route.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.finiteSiteWordRefinement`
(node `lem-sp-finite-site-word-refinement`).

No holes added, no split statements, and no `sorry` left in the delivered module.
The private generic inverse and localization lemmas are proved in full.
This repair changes no hole count: the retained proof closes the one original hole.
Used declarations may retain their own pre-existing obligations in their owning modules;
none is copied, weakened or re-stated here.

## No longer needed

Removed these proof imports:

- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.CategoryTheory.Adjunction.Mates`

The retained public imports are unchanged: they support the existing definitions and
statement. Their presence does not assert that this proof uses every declaration they export.

Pruned proof dependencies (these nodes remain in the project for any other consumers):

- `lem-sf-comparison-pullback-exact`: comparison inverse image on the fixed-ring ordinary
  module-sheaf category already has exactness instances; no ringed-presentation bridge.
- `lem-weil-pbc-module-sheaves-enough-injectives`,
  `lem-weil-pbc-dplus-injective-representative`, `def-weil-pbc-direct-image`, and
  `lem-weil-pbc-right-derived-plus-injective`: no representative is selected; intermediate
  derived functors already land in `DerivedCategory.Plus`, while the explicit lower-bound
  clauses use exactness directly.
- `lem-weil-pbc-affine-scheme-qcqs`,
  `lem-weil-pbc-locally-noetherian-quasi-separated`, and
  `lem-weil-pbc-qcqs-morphism-permanence`: proper morphisms already carry qcqs instances.
- `lem-weil-pbc-comparison-pullback`,
  `prop-weil-pbc-inverse-image-modules-exact`, and
  `prop-weil-pbc-proetale-constant-exact`: canonical direct-image composition and identity
  are already proved in `Sheaf.AlgebraicGeometry.ComparisonDirectImage`.
- `lem-sp-refinement-coefficient-mate` is not needed as a *proof* dependency: the needed
  fixed-coefficient site identity follows directly from `properOpenProEtaleIsoPlus`, whose
  real construction is exactly the three-constituent comparison. The existing statement
  dependency and public import are retained; no coefficient-refinement node is withdrawn.

No module is withdrawn or deleted. There is no claim that any of these modules is globally
unreachable: pruning here concerns this theorem's proof route.

## Where the brief, the DAG or earlier work was wrong

The planned injective-resolution construction and a fresh derivation of proper mate
coherence are unnecessary for the displayed Lean statement. Existing canonical coherence
lemmas provide the latter, and `D+` supplies boundedness for intermediate objects.
The plan's final site equation can be obtained by expanding the published construction,
without using the stronger scalar-change/refinement theorem. No false statement was found,
no target statement changed, and no blueprint unit route was bypassed.

The return at head `e4549ccd2d4` identified three apparently duplicate statements:
`derivedNatIso_symm`, `derivedId_fac`, and `square_identity`. In
`Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`, those helpers are private
and use section binders `[Category C] [Category D]`, which equate each category's object
and morphism universes. The retained helpers used `[Category* C] [Category* D]` instead:
the small-site sheaf category has object universe `u + 2` and morphism universe `u + 1`.
Those are different elaborated signatures, and the equal-universe helpers do not apply.
Following the return's explicit-binder remedy, all five generic helper signatures now
bind `{C : Type uC} [Category.{vC} C]` (and the other categories) directly, without
section variables. This makes the existing generality visible at every declaration.
All three reported names are repaired, as are the two related generic helpers.
The existing etale module and its private declarations are unchanged.
Validation: `lcompile.py` compiled the repaired item successfully in 25.9 seconds,
with no Lean errors or warnings. The source comparison confirms all seven definitions,
the main theorem statement and public imports match the current repository verbatim.

No new nodes or mathematical definition/interface repairs are included. The conservative
preflight command gate requires a change record for scoped proof-context commands:
`coord/changes/Y5-finite-site-private-proof-context.md`. It documents their local scope,
unchanged public signatures, explicit universe binders and consumer search (zero current
Lean importers).

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
