## What changed

Filled `AlgebraicGeometry.ProEtale.specifiedExceptionalRealization_shift` using the
canonical right-derived adjunction shift theorem, a private comparison of bounded-below
and unbounded derived shifts, and a private shift calculation for the relative Hom chain.
The generic realization calculation applies the normalized Hom formula to the counit, then
cancels invertible shift maps. The public theorem instantiates this calculation, avoiding
expensive unfolding of the geometric functors during checking. All helpers are proved and private. The proof privately imports bounded-below base-change
shifts, ordinary etale adjunction shifts, and the canonical right-derived adjunction shift
module (including its proved private unit helper).
The existing theorem signature and public imports are unchanged. Only the item module and
its own DAG node are changed.

Validation: the full proof compiled on the server in 17.4 seconds. The existing signature
and public imports were compared with the repository source and are unchanged. Debug
profiler options and unused tactics were then removed for delivery.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.specifiedExceptionalRealization_shift`
(`lem-sf-specified-exceptional-realization-shift`), the item's one original hole.
Added holes: none. Remaining holes in delivered Lean files: none.

## No longer needed

The planned lift of G's shifts through RX and subsequent comparison by uniqueness are
unnecessary: the normalized counit directly determines the desired rG shift square.
Consequently the proof does not call `Functor.CommShift.ofComp` or
`Functor.CommShift.ofComp_compatibility`.

`lem-sf-class-compact-support-comparison` and `thm-weil-pbc-site-comparison` are no
longer direct proof dependencies of this node. The concrete comparison and Hom equivalence
are already constructed in `SpecifiedExceptionalClassHom` and its imports. Those construction
dependencies stay; no module or declaration is withdrawn and no global pruning is claimed.
No original import was removed. Separate proof imports of
`WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor` and
`WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction` are unnecessary:
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift` publicly imports them.

## Where the brief, the DAG or earlier work was wrong

The node's second step suppressed the proof that the prescribed bounded-below/unbounded
comparison maps respect the fixed shifts. This is now an explicit private proof using
injective representatives and the defining comparison-unit equation. The helper allows any
unbounded shift structure whose unit commutes with shifts, preserving the adjunction-induced
ordinary etale shifts and the canonical pro-etale derived shifts. Associators omitted in the fixed direct-image formula are inserted in its shift proof;
their equality with the original comparison is proved componentwise. No hypothesis or
mathematical statement was changed. The existing canonical right-derived adjunction shift
theorem supplies the required derived comparison normalization.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
