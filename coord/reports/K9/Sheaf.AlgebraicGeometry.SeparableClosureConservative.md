## What changed

Proved `AlgebraicGeometry.separableClosure_baseChange_conservative` with its signature
unchanged. The field map associated to a geometric point gives an algebra structure
on its field; `IsAlgClosed.lift` extends this map to the separable closure.
`pullback.lift` then constructs the geometric lift with the same field.

For sheaves, `upperStarCompUliftSheafFiberIso` identifies the stalk of the pulled-back
morphism at a lift with its original geometric stalk. The existing conservative
family of universe-lifted geometric points detects invertibility. For unbounded
derived objects, `mapDerivedCategoryNatIso` and `mapDerivedCategoryCompIso` transport
the sheaf composition comparison to the unbounded derived category; applying
`stalk_faithful_derived` finishes the proof. Both forward implications are functorial.

Updated the item's DAG proof and proof dependencies to reflect the direct stalk
comparison. Added the private proof import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`. Existing public imports,
declaration signatures, and definitions are unchanged. No consumer adaptations or
change records are necessary. The unit record has no realized statement or steps
that this proof bypasses.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.separableClosure_baseChange_conservative`
(node `lem-kun-sep-closure-conservative`). Proved 1 of 1 original sorries;
0 holes added, 0 split off, and 0 sorries remain in the delivered Lean file.
The proof uses existing library declarations without adding any assumed theorem.

The completed file compiled successfully through `lcompile.py`; delivery preflight
also checks declaration axioms. The argument permits arbitrary geometric fields,
including arbitrary characteristic and transcendental extensions. It needs only
algebraicity of the given separable closure. Empty schemes cause no exception:
all pointwise detection obligations are vacuous, as required by the conservative
family criterion. No boundedness hypothesis is introduced in the derived clause.

## No longer needed

Removed the private proof import `Sheaf.AlgebraicGeometry.GeometricStalkAsPullback`
and its proof dependency `lem-kun-stalk-as-pullback`: the direct, already proved
pullback–stalk comparison supplies exactly the needed natural isomorphism.
This is local pruning; other consumers may still need that module.

Removed the redundant private proof imports
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`,
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, and
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`. The existing public API
already supplies pullbacks and the exactness instances used by the derived functor.
The exactness and derived-factorization mathematical dependencies remain in the
node because the derived comparison APIs use them. No modules are withdrawn,
and all existing public imports remain verbatim.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original proof plan requested a separate
geometric-point/global-sections identification for the sheaf clause; the existing
universe-lifted pullback–stalk API makes that detour unnecessary. Its generic
pullback–stalk node `lemma-openclosed-stalk-upperstar` is already proved and is
recorded as the replacement dependency. The unbounded derived comparison in the
plan is already implemented by the source library, so no new intermediate
statement or chain-level construction is needed in this item.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
