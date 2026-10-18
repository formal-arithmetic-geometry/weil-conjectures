## What changed

Proved both declarations of `Sheaf.Paper.ProperUnboundedWindowBounded`, preserving every
signature and every public import. The shortest route is the already proved
`CondensedRing.condensed_boundedBelow_preservesCoproduct` in
`Sheaf.AlgebraicGeometry.EllAdicProperBoundedBelowCoproducts`: properness supplies qcqs,
and the left disjunct of `hbound` supplies the common lower cohomology bound `a`.
The new proof constructs the source cofan from ambient derived coproducts and takes its
image under the actual derived functor as the target cofan. Colimit preservation gives
its universality. The requested canonical comparison is its own universal desc, hence
is the identity by colimit hom-ext. Both coefficient rings are handled separately.

Added proof-only imports of `Sheaf.AlgebraicGeometry.EllAdicProperBoundedBelowCoproducts`
and `Sheaf.CategoryTheory.GrothendieckDerivedCoproducts`. Kept the derived t-structure proof import; properness already publicly imports
the needed qcqs instances. Updated only `proof`, `proof_deps`
and `proof_origin` in the existing node `det-proper-unbounded-window-ii-bounded`.
No definitions, statements, public interfaces, other modules or unit records changed.

The supplied cofans work also for empty I, a=b and b<a. No nonempty or ordered-interval
hypothesis is introduced. The stronger input does not require ind-constructibility or
the common upper bound; `have _ := hM` records the supplied hypothesis without
changing either statement. No data is chosen from an unproved existence theorem.

Validation: the server single-file compiler accepted both proofs; delivery preflight
also checks the final module and its axiom probe. All Lean lines are at most 100 characters.

## Proved and sorry left

Closed both of the original two holes, at node `det-proper-unbounded-window-ii-bounded`:

- `AlgebraicGeometry.ProEtale.properUnboundedWindowBounded`.
- `AlgebraicGeometry.ProEtale.properUnboundedWindowBounded_padicAlgCl`.

Sorry left in the item: none. Holes added: zero. Split-off theorems: zero.
This is a proof from existing library declarations, not a decomposition. Dependencies
elsewhere in the existing library may still rest on sorry; none is added by this delivery.

## No longer needed

Removed these direct proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`.

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`.
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`.
- `Sheaf.AlgebraicGeometry.ProperHeartContinuityDirectImage`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`.
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`.
- `WeilConjectures.CategoryTheory.TruncationTriangle`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`.

Removed these old direct DAG proof dependencies:

- `def-weil-finite-type-morphism`.

- `prop-pur-kinjective-resolutions-exist`.
- `sk-def-sfb-module-pushforward-pullback`.
- `sk-def-sfb-module-derived-pushpull`.
- `lem-pc-right-derived-functor-triangulated`.
- `lem-sp-grothendieck-enough-injectives`.
- `lem-kun-grothendieck-derived-coproducts`.
- `def-weil-abstract-derived-category`.
- `det-ambient-ind-derived-sums`.
- `det-proper-heart-continuity-direct-image`.
- `lem-weil-pbc-unbounded-derived-iso-cohomology`.
- `lem-sf-derived-concentrated-single`.
- `lem-sp-derived-functor-single-identification`.
- `src-right-derived-functor-plus-compatibility`.
- `def-kun-truncations`.
- `lem-weil-pbc-truncation-triangle`.
- `lem-sf-triangle-morphism-iso`.

The bounded-below theorem replaces the separate shifted-heart calculation, truncation
induction, sum-of-triangles calculation and five-lemma glue in this module. In particular,
`Sheaf.Paper.AmbientIndDerivedSums` (already absent from the original imports) and
`Sheaf.Paper.CondensedModuleDerivedPushpull` are not additionally imported for that plan.
`lem-sfb-adic-proper-bounded-below-coproducts` and
`lem-grothendieck-derived-has-coproducts` provide the stronger preservation statement and
coproduct existence respectively. Module-object Grothendieck abelianness supplies the
underlying-category colimits directly. These are removals from this module's direct
route; they do not assert that other parents cease to need those nodes or that the
removed modules disappear from the whole targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The planned induction is unnecessary given the published bounded-below condensed-module
coproduct theorem. That theorem applies to exactly the same internal module categories,
coefficient universe and total right derived functor, with fewer hypotheses. The unit's
bounded-family assertion remains proved and available for its later arbitrary-family
step; no unit statement or step is removed. No mathematical statement was found false
and no definition repair or forced consumer adaptation was needed.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
