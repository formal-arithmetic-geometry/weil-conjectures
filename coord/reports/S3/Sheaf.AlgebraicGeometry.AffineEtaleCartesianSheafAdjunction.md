## What changed

Proved `AlgebraicGeometry.Scheme.affineEtale_cartesian_sheafAdjunction` with its
signature unchanged. The cartesian object isomorphisms are natural by the two
pullback projections. The continuous pushforward is compared explicitly with
ordinary étale direct image, and the adjunction is conjugated by the two affine
restriction equivalences. All finite-limit preservation steps compile.

Added `Sheaf.AlgebraicGeometry.EtaleInverseImageSmallUniverse` and proved
`AlgebraicGeometry.Scheme.etale_setPullback_small`. Its proof bounds the section
set using the small conservative family of geometric points, the pullback-stalk
and coefficient-ULift comparisons, and sheaf Yoneda. The item's private theorem
`etale_smallUniverse_sheafAdjunction` uses this bound to shrink the actual ordinary
inverse image, restrict its adjunction through fully faithful ULift, and descend
finite-limit preservation. These are actual constructions and proved isomorphisms;
there is no data definition using `sorry` or an arbitrary unproved existence.

The route retains the DAG's ordinary étale adjunction and affine restriction
steps and changes no blueprint unit statement or realized step. Only proof
imports changed. Sources read online: Stacks [03Q0](https://stacks.math.columbia.edu/tag/03Q0),
[03Q1](https://stacks.math.columbia.edu/tag/03Q1), and
[04HR](https://stacks.math.columbia.edu/tag/04HR),
[03PU](https://stacks.math.columbia.edu/tag/03PU), and
[03PT](https://stacks.math.columbia.edu/tag/03PT). The local Stacks TeX is absent.
Both delivered modules pass sandbox compilation in import order.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.affineEtale_cartesian_sheafAdjunction`
(`lem-weil-pbc-affine-etale-cartesian-sheaf-adjunction`).

Added and proved `AlgebraicGeometry.Scheme.etale_setPullback_small`
(`lem-weil-pbc-etale-inverse-image-small-universe`). No new holes were added;
no `sorry` remains in either delivered module. The private helpers are proved.
The existing imported affine restriction equivalence and inclusion continuity
remain dependencies; this delivery does not close their upstream holes.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (still reached through
  the existing affine-topos module, so its removal is only a direct-import cleanup).

The algebraic group/ring lift branches are unnecessary for this set-sheaf result.
The following modules leave this item's import closure; other targets/users may
still need them. All their associated DAG nodes are listed where applicable:

- `Mathlib.Algebra.Category.Grp.Limits`
- `Mathlib.Algebra.Category.Ring.FilteredColimits`
- `Mathlib.Algebra.Category.Ring.Limits`
- `Mathlib.CategoryTheory.IsoCat`
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`
- `Mathlib.CategoryTheory.Monoidal.CommGrp_`
- `Mathlib.CategoryTheory.Monoidal.CommMon_`
- `Mathlib.CategoryTheory.Monoidal.Ring`
- `Mathlib.CategoryTheory.Sites.Adjunction`
- `Mathlib.CategoryTheory.Sites.CartesianMonoidal`
- `Sheaf.AlgebraicGeometry.EtaleAbelianDirectImageInternal`: `lem-weil-pbc-etale-abelian-direct-image-internal`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAbelianLift`: `lem-weil-pbc-etale-inverse-image-abelian-lift`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAbelianLiftHom`: `lem-weil-pbc-etale-inverse-image-abelian-lift-hom`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAbelianLiftOperations`: `lem-weil-pbc-etale-inverse-image-abelian-lift-ops`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`: `lem-weil-pbc-etale-inverse-image-algebraic-structures`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageRingAdjunction`: `lem-weil-pbc-etale-inverse-image-ring-adjunction`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageRingLift`: `lem-weil-pbc-etale-inverse-image-ring-lift`
- `Sheaf.AlgebraicGeometry.EtaleRingInverseImageCounit`: `lem-weil-pbc-etale-ring-inverse-image-counit`
- `Sheaf.AlgebraicGeometry.EtaleRingInverseImageUnit`: `lem-weil-pbc-etale-ring-inverse-image-unit`
- `Sheaf.CategoryTheory.Adjunction.FiniteProductRingFunctor`: `lem-weil-pbc-finite-product-ring-functor`
- `Sheaf.CategoryTheory.Adjunction.LiftedCommGrpBranch`: `lem-weil-pbc-lifted-comm-group-branch`
- `Sheaf.CategoryTheory.Adjunction.LiftedCommRingBranch`: `lem-weil-pbc-lifted-comm-ring-branch`
- `Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`: `lem-weil-pbc-adjunction-lifts-group-ring-objects`
- `Sheaf.CategoryTheory.Adjunction.RingAdjunctPreservesOperations`: `lem-weil-pbc-ring-adjunct-preserves-operations`
- `Sheaf.CategoryTheory.Adjunction.RingCoadjunctPreservesOperations`: `lem-weil-pbc-ring-coadjunct-preserves-operations`
- `Sheaf.CategoryTheory.Adjunction.RingHomEquivCore`: `lem-weil-pbc-ring-hom-equiv-core`
- `Sheaf.CategoryTheory.SheafRingObjectsBijective`: `lem-weil-pbc-sheaf-ring-objects-bijective`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresAbelian`: `lem-weil-pbc-sheaf-algebraic-structures-abelian-component`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`: `lem-weil-pbc-sheaf-algebraic-structures-objects`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresRing`: `lem-weil-pbc-sheaf-algebraic-structures-ring-component`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresRingCore`: `lem-weil-pbc-sheaf-algebraic-structures-ring-core`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresRingMorphism`: `lem-weil-pbc-sheaf-algebraic-structures-ring-morphism`

## Where the brief, the DAG or earlier work was wrong

The DAG's step 3 said to use the algebraic-structures inverse-image theorem
throughout at Type u, but its actual Lean set functor has coefficients Type(u+1).
It cannot supply the stated Type u adjunction by specialization. The new proved
smallness result and the fully proved shrinking/adjunction restriction repair
this interface gap. The finite-limit statement itself is unchanged. Neither
being affine nor nonempty was used in the new size theorem: for an empty base
its family of geometric points is empty and joint faithfulness still gives the
required bound. Identity morphisms reduce to the usual coefficient lift and
shrinking comparisons. No separation or finiteness hypothesis was added.

## New nodes

`lem-weil-pbc-etale-inverse-image-small-universe` records the proved size bound
for the actual ordinary étale inverse image of a coefficient-lifted Type u
sheaf. It is strictly a part of the argument: it asserts only smallness of
section sets, and asserts neither the affine-site comparison, the adjunction,
nor its finite-limit preservation. Module:
`Sheaf.AlgebraicGeometry.EtaleInverseImageSmallUniverse`.
No change record is needed: no existing statement or public import changed.

## Second reading by S3

1. Compared the delivered module with the repository version. The target
   signature is byte-for-byte unchanged; only its proof and proof-only imports
   changed. The added small-universe module is recorded by its new DAG node.
   Verdict: pass.
2. Compiled both delivered modules in import order with `lcompile.py`; no
   errors, warnings, `sorry`, or forbidden declarations occur in the delivered
   sources. The target's remaining `sorryAx` dependency comes only from open
   imported statements. Verdict: pass.
3. Checked the new `etale_setPullback_small` statement against its edge cases
   and source argument. It asserts only the required smallness property, is
   strictly below the target, and has a matching node and docstring. No
   duplicate library declaration was found. Verdict: pass.
4. The proof follows the ordinary étale adjunction, explicit shrinking, and
   affine restriction equivalences. The direct algebraic-structures imports
   were pruned; the unit route and finite-limit claim remain intact. Verdict:
   pass.
5. The target node's proof, dependencies, and origin match the Lean proof, and
   the new node carries the required Lean record and source metadata. Verdict:
   pass.

Changed during second reading: no Lean statements or proofs; appended this
review record only.
