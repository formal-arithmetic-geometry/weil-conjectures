## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.formal_closed_support_derived` with its
signature unchanged. Finite type over the field gives Noetherianity and hence a quasi-compact
open complement. The sheaf-support theorem supplies additivity, exactness and the adjunction.
A private, fully proved helper constructs the Hom-complex isomorphism degreewise and checks
both differential terms using the additive Hom adjunction.

The existing broader support node supplies injective-unit epimorphy, the natural triangle,
and the explicit fibre theorem. Three fully proved private helpers transfer epimorphy,
triangles, and mapping cones along the uniqueness isomorphisms of adjoints. The triangle
helper explicitly checks all three squares, so its arrows are exactly the required derived
counit and unit. The fibre comparison uses the actual sheaf-level unit and its shifted cone.
No definitions, existing signatures or other modules were changed.

The item DAG copy records this shorter proof. Its unit route is retained: the unit itself
explicitly cites the broader support-adjunction node. Existing public re-exports removed
below are already publicly re-exported by the retained CondensedClosedSupportAdjunction
import. New proof imports are Adjunction.Additive, Adjunction.Unique, and
AlgebraicGeometry.Noetherian; Triangulated.Triangulated remains needed by the triangle helper.

The public-import pruning is documented in
`coord/changes/formal-closed-support-derived-imports.md`. All four redundant public
imports remain public through CondensedClosedSupportAdjunction; consumer meanings are unchanged.
The change record lists the item and all 275 transitive consumers from downstream.py,
with current claim holders; no adaptations are needed.

Validation: on resuming the retained sandbox on 2026-10-19, the proof with all import
pruning compiled cleanly through lcompile.py in 17.4 seconds. The existing theorem
signature was compared verbatim with the current shared source and is unchanged.
The delivered Lean file has no sorry and every line is at most 100 characters.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.CondensedRing.formal_closed_support_derived`
(node `det-lem-formal-closed-support-derived`). Added 0 holes; split off 0 theorems.
No sorry remains in any delivered Lean file. Existing dependencies retain their own proofs
or registered holes; none was copied or restated.

## No longer needed

Removed direct imports:

- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits`
- `Mathlib.RingTheory.FiniteType`
- `Mathlib.RingTheory.Spectrum.Prime.Noetherian`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`

The last two imports were added to the shared source after the retained proof was written.
They are also unnecessary directly: the proof uses no bounded-constructibility API, and
UpperLowerStar.Defs remains public through CondensedClosedSupportAdjunction.

Removed direct proof dependencies:

- `lem-wf-affine-noetherian-components`
- `def-weil-quasi-separated-morphism`
- `lem-weil-pbc-ring-sheaves-grothendieck`
- `lem-pur-kinjective-degreewise-existence`
- `def-sfb-right-derived-functor`
- `det-sf-open-closed-sequence-ring-sheaf`
- `lem-weil-pbc-right-adjoint-preserves-kinjective`
- `lem-weil-pbc-complex-ses-triangle`
- `lem-sf-exact-functor-derived-triangulated`
- `lem-weil-pbc-termwise-adjunction-homotopy`
- `lem-weil-pbc-kinjective-hom-derived`
- `det-sf-open-closed-pullback-limits`
- `lem-sf-triangle-morphism-iso`

Removed the obsolete direct `tool_uses` approvals for each removed dependency above that
was previously listed there. Retained `det-lem-formal-closed-support-adjunction`.

The explicit K-injective-resolution/short-exact-sequence/rotation argument is already
encapsulated by the broader node's labelled triangle and fibre theorem. These are therefore
not needed directly in this module. Their use inside the broader dependency is retained;
this report does not claim that all these modules leave the targets' transitive closure.
The original Noetherian affine-chart argument is replaced by the existing Mathlib leaf
`lem-weil-pbc-finite-type-over-noetherian`. No Lean module was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG step 2 says the broader node's triangle has unlabeled arrows and cannot identify the
middle arrow. Its present Lean declaration `closedSupport_triangle` specifies precisely the
derived counit and unit; `closedSupport_fiber` also specifies the actual-unit mapping cone.
Using these existing declarations avoids duplicating their entire resolution argument.
The two support functors use different constructions of inverse image, so they are compared
by uniqueness of right adjoints rather than assumed definitionally equal. The two open units
are compared by uniqueness of left adjoints, which also gives the arrow isomorphism needed
for their mapping cones. No statement repair or new node was necessary.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
