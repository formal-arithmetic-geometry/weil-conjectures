## What changed

Kept all existing declarations, signatures, visibility and eight concrete comparison definitions.
In Sheaf.Paper.MateOpenRestriction, constructed the restricted open adjunction and its
unique counit-compatible comparison, proved the source-open comparison by transporting
the composite adjunction along the actual source compositor, and proved open-cover
conservativity from the existing condensed-cover theorem. The passage from constructible
finite-Tor generators to the full localizing closure is a complete Lean proof using the
defining intersection, exactness and preservation of every existing coproduct.
Added and proved Sheaf.Paper.OpenPullbackGenerators: pull back the finite stratification and
its constant-model covers, transport along the coefficient compositors, and apply the existing
exact-functor boundedness and flat-preserving Tor-amplitude lemmas.
Both sandbox modules compile together through lcompile.py (4.7 s for the helper in the
resumed check; the earlier combined check took 3.4 s and 8.0 s respectively).
Added proof-only imports CondensedCoverRestrictionConservative,
FiniteCoefficient.Derived.OpenCover, OpenPullbackGenerators and Adjunction.Restrict.
All existing public imports are unchanged.

## Proved and sorry left

Original holes: 4. Closed original holes (namespace
AlgebraicGeometry.ProEtale.CondensedRing): mateOpenImmersion,
mateOpenSourceRestriction, mateOpenCover_isIso. Added and proved
AlgebraicGeometry.ProEtale.CondensedRing.openPullback_generators
(lem-sfb-open-pullback-generators), with zero new holes. The only remaining hole is the
unchanged AlgebraicGeometry.ProEtale.CondensedRing.mateOpenTargetRestriction
(det-sf-mate-open-restriction).

Net source holes: 4 to 1, with no split-off holes. These proofs use existing library
declarations whose own dependencies may still contain sorry; this is not a claim that
their transitive axioms are sorry-free. The remaining target-open theorem needs the
base-changed exceptional adjunction and the precisely normalized comparison equation.
Empty and identity opens, empty covers, zero generators and arbitrary cover index universes
are included. No data is chosen from an unproved mere existence theorem.

## No longer needed

Removed proof-only imports:

- Sheaf.Paper.UnboundedLocalizingPullback
- Sheaf.Paper.LocalizingLowerShriekComposition
- Sheaf.Paper.NonrationalLocalizingLowerShriekComposition
- Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd
- Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro
- Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
- Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
- Sheaf.Paper.CondensedModuleDerivedPushpull
- Sheaf.Paper.CartesianCoefficients
- Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
- WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
- WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
- Mathlib.CategoryTheory.Yoneda
- Mathlib.CategoryTheory.Triangulated.Pretriangulated
- Mathlib.CategoryTheory.Adjunction.Basic
- Mathlib.CategoryTheory.Sites.LocalProperties
- Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
- Mathlib.Algebra.Homology.DerivedCategory.Basic
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType
- Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
- Mathlib.AlgebraicGeometry.Morphisms.Separated
- Mathlib.AlgebraicGeometry.Morphisms.Proper
- Mathlib.AlgebraicGeometry.Sites.Fpqc
- Mathlib.AlgebraicGeometry.Sites.Proetale
- Mathlib.Topology.Constructible
- Sheaf.SixFunctorsBasics.BrownHypotheses

The proved generator helper also avoids its earlier planned dependencies
det-lem-int-tensor-projection, lem-sfb-pullback-constant-model-constructible,
sk-def-sfb-module-lower-shriek and sk-prop-sfb-cartesian-coefficients: explicit
cover/stratification pullback and flat-model preservation replace that route.

Direct proof dependencies removed from the parent node (some remain below the retained
helper or target-open plan; this does not claim they are globally unreachable):

- def-pc-essentially-constant-ind-diagram
- def-pc-essentially-constant-pro-diagram
- def-sfb-finite-extension-by-zero-adjunction
- def-sfb-finite-upper-star
- def-weil-abstract-derived-category
- def-weil-constructible-subset
- def-weil-pbc-composite-adjunction
- def-weil-pbc-fpqc-covering
- def-weil-pbc-small-proetale-site
- def-weil-proper-morphism
- det-proper-base-change-unbounded-pullback
- lem-galois-yoneda-fully-faithful
- lem-kun-distinguished-cone-zero
- lem-pc-derived-adjoint-functors
- lem-sfb-sheaf-cover-local-isomorphism
- lem-weil-pbc-exact-functor-complex-cohomology
- lem-weil-pbc-exact-functor-derived-factorization
- lem-weil-pbc-exact-functor-derived-functor
- lem-weil-pbc-termwise-adjunction-homotopy
- lem-weil-proetale-weakly-etale-localization
- sk-prop-sfb-cartesian-coefficients

Withdrawn obsolete parent tool_uses approvals (original order):

- sk-prop-sfb-cartesian-coefficients
- lem-pc-derived-adjoint-functors
- det-proper-base-change-unbounded-pullback
- lem-galois-yoneda-fully-faithful
- def-weil-pbc-composite-adjunction
- def-weil-constructible-subset
- lem-kun-distinguished-cone-zero
- lem-weil-pbc-exact-functor-complex-cohomology
- lem-weil-proetale-weakly-etale-localization
- def-weil-pbc-small-proetale-site
- lem-sfb-sheaf-cover-local-isomorphism
- def-weil-abstract-derived-category
- def-weil-proper-morphism
- def-weil-finite-type-morphism
- def-pc-essentially-constant-ind-diagram
- def-pc-essentially-constant-pro-diagram
- def-sfb-finite-extension-by-zero-adjunction
- def-sfb-finite-upper-star
- def-weil-pbc-fpqc-covering
- lem-weil-pbc-exact-functor-derived-factorization
- lem-weil-pbc-exact-functor-derived-functor
- lem-weil-pbc-termwise-adjunction-homotopy

The implemented open adjunction uses the existing upstream derived adjunction, so it
does not reprove its ind/pro descent. The source comparison uses the concrete same-proper-map
compositor, so it does not need the general rational/nonrational composition theorem.
The cover clause uses existing condensed-cover conservativity, so its cone, cohomology
and site-locality argument is not duplicated. The original unit's four comparisons
are retained. No globally unreachable module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The recorded proof sketches do not directly supply preservation
for an arbitrary admissible ring object: unboundedLocalizingPullback has concrete
coefficient specializations, whereas this module uses coefficients up to monoid-object
isomorphism; pullback_constantModelConstructible uses another ring-sheaf presentation.
The new generator lemma proves that missing glue directly, rather than pretending that
the concrete specialization applies definitionally. Its Tor-amplitude part uses the existing
proved flat-preservation API, so the open projection-formula step of the earlier plan is
unnecessary. The resumed dry run found the missing LeanSearch record; it is now supplied.
The unit-route BoundaryRefinement import is retained. No existing statement was changed.
For the retained target-open hole, the composition declarations supply isomorphisms coherent
under refinements, but do not state their relation to the explicit mateOpenTargetLowerShriek
map. That precise normalization still needs its open proper/direct-image adjunction
calculation; an arbitrary comparison isomorphism does not discharge the equation.
The node's original derived-adjunction and cover-detection steps already have reusable
Lean interfaces, enabling the shorter formal proofs here.

## New nodes

lem-sfb-open-pullback-generators, in sec-six-functors-basics/sk-lem-sf-mate,
records precisely bounded constant-model constructibility and finite Tor amplitude
under quasi-compact open inverse image. It is strictly a generator-level part of clause
(1), and does not contain an exceptional adjunction or any comparison/uniqueness conclusion.
It is proved, with no new sorry, and supports both the open-immersion and source-restriction
proofs. No change record is needed: no existing statement, definition or public import changed.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
