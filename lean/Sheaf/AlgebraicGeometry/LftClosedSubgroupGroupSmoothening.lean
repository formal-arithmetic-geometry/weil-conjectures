module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Universal smoothening of a locally finite type closed subgroup

Source: Bosch--Lutkebohmert--Raynaud, Neron Models, 7.1 Theorem 5, printed p.175,
and 10.1 Proposition 4 proof, printed p.291.
(blueprint: lem-sfb-lft-closed-subgroup-group-smoothening)

The open subgroup `M0` is specified by its geometric fibres: its image on each
geometric fibre is exactly the connected component of the identity. The universal
property uses ordinary morphisms of schemes over the base, with no group structure
or quasi-compactness imposed on the smooth test scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A flat closed subgroup with smooth finite type generic fibre admits a group smoothening.

Source: BLR, Neron Models, 7.1 Theorem 5 and 10.1 Proposition 4 proof.
(blueprint: lem-sfb-lft-closed-subgroup-group-smoothening)

Proof plan from the accepted DAG split:
1. The closed subgroup `C` is locally of finite type by the affine quotient description
   of a closed immersion, and separated by pulling back the diagonal of `M`.
   By lem-sfb-group-smoothness-identity-criterion its nonsmooth fibres lie over a
   finite set of closed points. If that set is empty, use the identity of `C`.
2. At each remaining point repeatedly dilate the canonical subgroup supplied by
   lem-sfb-canonical-group-dilatation-defect-drop, using
   lem-sfb-group-dilatation-universal-property. If the initial identity defect is `r`,
   induction gives defect at stage `n` at most `max(0,r-n)`. After `r` steps it is zero,
   so the identity criterion gives smoothness on this fibre, also when `r = 0`.
3. Perform this finite construction at the finitely many bad fibres. Each dilatation
   is an isomorphism away from its centre fibre, so earlier smoothness persists.
   The composite `u` preserves the generic fibre and all the asserted group,
   separatedness and local finite type structures.
4. For any smooth test scheme, its map into the current group factors on the centre
   fibre through the canonical subgroup (the defect-drop lemma). The dilatation
   universal property gives a unique lift at each step. Induction gives existence
   of a lift to `N`; stage-by-stage uniqueness gives injectivity on the ordinary
   Hom sets. No Neron mapping property or quasi-compactness of a test is used. -/
theorem lft_closed_subgroup_group_smoothening
    (D : Type u) [CommRing D] [IsDedekindDomain D] (hdim : ringKrullDim D = 1)
    (E : Type u) [Field E] [Algebra D E] [IsFractionRing D E]
    (M : Grp (Over (Spec (.of D)))) [IsCommMonObj M.X]
    [Smooth M.X.hom] [IsSeparated M.X.hom] [LocallyOfFiniteType M.X.hom]
    (M0 : Grp (Over (Spec (.of D)))) (i0 : M0 ⟶ M)
    [IsOpenImmersion i0.hom.hom.left]
    [LocallyOfFiniteType M0.X.hom] [QuasiCompact M0.X.hom]
    (hM0 : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ Spec (.of D)),
      Set.range ((Over.pullback s).mapGrp.map i0).hom.hom.left =
        connectedComponent (GrpObj.onePoint ((Over.pullback s).mapGrp.obj M).X))
    (C : Grp (Over (Spec (.of D)))) [IsCommMonObj C.X]
    (i : C ⟶ M) [IsClosedImmersion i.hom.hom.left] [Flat C.X.hom]
    [Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).obj C.X).hom]
    [LocallyOfFiniteType
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).obj C.X).hom]
    [QuasiCompact
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).obj C.X).hom] :
    ∃ (N : Grp (Over (Spec (.of D)))) (_ : IsCommMonObj N.X) (u : N ⟶ C),
      Smooth N.X.hom ∧ IsSeparated N.X.hom ∧ LocallyOfFiniteType N.X.hom ∧
      IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).mapGrp.map u) ∧
      ∀ (X : Over (Spec (.of D))), Smooth X.hom →
        Function.Bijective (fun f : X ⟶ N.X => f ≫ u.hom.hom) := by
  sorry

end AlgebraicGeometry
