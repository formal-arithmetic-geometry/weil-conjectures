/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.MvPolynomial.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.SupportDimension
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import all Sheaf.AlgebraicGeometry.Sites.AffineLineProjectionStalkBound
import Sheaf.AlgebraicGeometry.Sites.AffineInfinityBoundarySupport
import Sheaf.AlgebraicGeometry.Sites.ProjectiveLineBoundedTorsionVanishing
import Mathlib.Algebra.MvPolynomial.Equiv
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.OpenClosed.Supported
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import WeilConjectures.CategoryTheory.Abelian.ExactFunctorHigherDerivedVanishing
import WeilConjectures.AlgebraicGeometry.Sites.LerayVanishing

/-! # The higher-degree projection support calculation

Source: blueprint thm-sc-affine-torsion-cd, compactification and Leray argument.
(blueprint: lem-sc-affine-polynomial-higher-projection-support)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

private theorem polynomialProjection_affineLine_iso
    (K : Type u) [CommRing K] (m : ℕ) :
    let B := Spec (.of (MvPolynomial (Fin m) K))
    let f := Spec.map (CommRingCat.ofHom (MvPolynomial.rename
      (Fin.succ : Fin m → Fin (m + 1))).toRingHom)
    ∃ e : Spec (.of (MvPolynomial (Fin (m + 1)) K)) ≅ AffineSpace PUnit.{u + 1} B,
      e.hom ≫ AffineSpace PUnit.{u + 1} B ↘ B = f := by
  let A := MvPolynomial (Fin m) K
  let E : MvPolynomial (Fin (m + 1)) K ≃+* MvPolynomial PUnit.{u + 1} A :=
    (MvPolynomial.finSuccEquiv K m).toRingEquiv.trans
      (MvPolynomial.uniqueAlgEquiv A PUnit.{u + 1}).symm.toRingEquiv
  let e := (Scheme.Spec.mapIso E.toCommRingCatIso.op).symm ≪≫
    (AffineSpace.SpecIso PUnit.{u + 1} (.of A)).symm
  refine ⟨e, ?_⟩
  change Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫
    (AffineSpace.SpecIso PUnit.{u + 1} (.of A)).inv ≫ _ = _
  rw [AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  change E.symm.toRingHom.comp MvPolynomial.C =
    (MvPolynomial.rename (Fin.succ : Fin m → Fin (m + 1))).toRingHom
  apply RingHom.ext
  intro p
  apply E.injective
  change E (E.symm (MvPolynomial.C p)) =
    E ((MvPolynomial.rename (Fin.succ : Fin m → Fin (m + 1))) p)
  rw [E.apply_symm_apply]
  induction p using MvPolynomial.induction_on with
  | C r =>
      rw [MvPolynomial.rename_C]
      change MvPolynomial.C (MvPolynomial.C r) =
        (MvPolynomial.uniqueAlgEquiv A PUnit.{u + 1}).symm
          ((MvPolynomial.finSuccEquiv K m) (MvPolynomial.C r))
      rw [MvPolynomial.finSuccEquiv_apply]
      simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
      exact ((MvPolynomial.uniqueAlgEquiv A PUnit.{u + 1}).symm.commutes _).symm
  | add p r hp hr => simpa only [map_add] using congrArg₂ (· + ·) hp hr
  | mul_X p i hp =>
      simp only [map_mul, hp]
      congr 1
      rw [MvPolynomial.rename_X]
      change MvPolynomial.C (MvPolynomial.X i) =
        (MvPolynomial.uniqueAlgEquiv A PUnit.{u + 1}).symm
          ((MvPolynomial.finSuccEquiv K m) (MvPolynomial.X i.succ))
      rw [MvPolynomial.finSuccEquiv_X_succ]
      exact ((MvPolynomial.uniqueAlgEquiv A PUnit.{u + 1}).symm.commutes _).symm

private theorem boundary_support
    {U Z Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (i : Z ⟶ Y) [IsClosedImmersion i] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (M : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (hq : 0 < q) :
    (Etale.lowerStar AddCommGrpCat.{u + 1} i).essImage
      (((Etale.lowerStar AddCommGrpCat.{u + 1} j).rightDerived q).obj M) := by
  apply Etale.mem_essImage_lowerStar_of_isZero_upperStar i hij
  have e₁ := Functor.rightDerivedCompObjIso
    (Etale.lowerStar AddCommGrpCat.{u + 1} j)
    (Etale.upperStar AddCommGrpCat.{u + 1} j) q M
  have e₂ := Functor.rightDerivedObjIsoOfIso
    (asIso (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).counit) q M
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  exact (Functor.isZero_rightDerived_obj_of_exact (𝟭 _) M r).of_iso (e₁.symm ≪≫ e₂)

private theorem boundary_mixed_zero
    {U Z Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (i : Z ⟶ Y) [IsClosedImmersion i] (g : Y ⟶ Z)
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (hig : i ≫ g = 𝟙 Z)
    (M : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) :
    IsZero (((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived p).obj
      (((Etale.lowerStar AddCommGrpCat.{u + 1} j).rightDerived q).obj M)) := by
  obtain ⟨V, ⟨e⟩⟩ := boundary_support j i hij M q hq
  let I := Etale.lowerStar AddCommGrpCat.{u + 1} i
  let G := Etale.lowerStar AddCommGrpCat.{u + 1} g
  have := Adjunction.preservesInjectiveObjects_of_preservesFiniteLimits
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i)
  let e₁ := Functor.compRightDerivedObjIso I G
    (fun V _ ↦ Functor.rightAcyclic_of_injective (I.obj V)) p V
  let e₂ := Functor.rightDerivedObjIsoOfIso
    ((Etale.lowerStarComp AddCommGrpCat.{u + 1} i g (𝟙 Z) hig.symm) ≪≫
      Etale.lowerStarId AddCommGrpCat.{u + 1} Z) p V
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  have hz : IsZero (((𝟭 (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})).rightDerived p).obj
      V) := by
    rw [hr]
    exact Functor.isZero_rightDerived_obj_of_exact (𝟭 _) V r
  exact (hz.of_iso (e₁.symm ≪≫ e₂)).of_iso ((G.rightDerived p).mapIso e.symm)

private theorem leray_pullback_zero
    {X Y S T : Scheme.{u}} (j : X ⟶ Y) (g : Y ⟶ S) (s : T ⟶ S)
    (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (r : ℕ)
    (hdiag : ∀ p q : ℕ, p + q = r →
      IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj
        (((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived p).obj
          (((Etale.lowerStar AddCommGrpCat.{u + 1} j).rightDerived q).obj M)))) :
    IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj
      (((Etale.lowerStar AddCommGrpCat.{u + 1} (j ≫ g)).rightDerived r).obj M)) := by
  let J := Etale.lowerStar AddCommGrpCat.{u + 1} j
  let G := Etale.lowerStar AddCommGrpCat.{u + 1} g
  let P := Etale.upperStar AddCommGrpCat.{u + 1} s
  have hac := Adjunction.isAcyclicComposablePair
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j) (G ⋙ P)
  have hd : ∀ p q : ℕ, p + q = r →
      IsZero ((((G ⋙ P).rightDerived p).obj ((J.rightDerived q).obj M))) := by
    intro p q hpq
    exact (hdiag p q hpq).of_iso (Functor.rightDerivedCompObjIso G P p _)
  have hz := Functor.isZero_rightDerived_comp_of_isZero J (G ⋙ P) hac M r hd
  let e₁ := Functor.rightDerivedObjIsoOfIso
    (Functor.associator J G P).symm r M
  let e₂ := Functor.rightDerivedCompObjIso (J ⋙ G) P r M
  let e₃ := Functor.rightDerivedObjIsoOfIso
    (Etale.lowerStarComp AddCommGrpCat.{u + 1} j g (j ≫ g) rfl).symm r M
  exact hz.of_iso (P.mapIso e₃ ≪≫ e₂.symm ≪≫ e₁.symm)

/-- Vanishing away from the allowed support in degrees above two.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/
thm-sc-affine-torsion-cd.proof.md, compactification and Leray argument.
(blueprint: lem-sc-affine-polynomial-higher-projection-support)

Proof: Identify the polynomial projection with a relative affine line, compactify it in
P^1_B, and write j for its open chart, g for the projective projection and i for infinity.
Positive R^q j_* are supported on i. Exact closed direct image, its preservation of
injectives, and g i=id kill all mixed terms R^p g_*R^q j_* for p,q positive. The
projective-line bounded-torsion theorem kills the q=0 row in degrees above two. The
local infinity-boundary calculation kills the p=0 column at the specified point. After
exact inverse image the Leray diagonal thus vanishes; the composite direct image is zero
at that point. Testing after algebraic closure and the inverse-image/stalk comparison
extend the result to every separably closed geometric field. -/
theorem isZero_stalk_polynomialProjection_of_lowerDimension_of_gt_two
    (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ)
    (hIH : ∀ (L : Type u) [Field L] (m c : ℕ), m < n + 2 →
      (Spec (.of L)).HasTorsionCohomologicalDimensionLE c →
      ∀ (X : Scheme.{u}) [IsAffine X] (a : X ⟶ Spec (.of L))
        [LocallyOfFiniteType a] [QuasiCompact a],
        topologicalKrullDim X ≤ (m : WithBot ℕ∞) →
          X.HasTorsionCohomologicalDimensionLE (m + c))
    (M : Sheaf (Spec (.of (MvPolynomial (Fin (n + 2)) K))).smallEtaleTopology
      AddCommGrpCat.{u + 1}) (N : ℕ) (hN : 0 < N) (hM : N • 𝟙 M = 0)
    (q : ℕ) (hq : 2 < q) :
    let f : Spec (.of (MvPolynomial (Fin (n + 2)) K)) ⟶
        Spec (.of (MvPolynomial (Fin (n + 1)) K)) :=
      Spec.map (CommRingCat.ofHom (MvPolynomial.rename
        (Fin.succ : Fin (n + 1) → Fin (n + 2))).toRingHom)
    let b := Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin (n + 1)) K)))
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin (n + 1)) K))),
      ((n + 2 : ℕ) : Cardinal.{u}) < (q : Cardinal.{u}) +
          residueFieldTrdeg b (s (IsLocalRing.closedPoint Ω)) →
        IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj
          (((Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj M)) := by
  classical
  dsimp only
  intro Ω _ _ s hs
  let X := Spec (.of (MvPolynomial (Fin (n + 2)) K))
  let B := Spec (.of (MvPolynomial (Fin (n + 1)) K))
  let f : X ⟶ B := Spec.map (CommRingCat.ofHom (MvPolynomial.rename
    (Fin.succ : Fin (n + 1) → Fin (n + 2))).toRingHom)
  let b : B ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin (n + 1)) K)))
  let t : Spec (.of (AlgebraicClosure Ω)) ⟶ B :=
    Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω))) ≫ s
  have ht : t (IsLocalRing.closedPoint (AlgebraicClosure Ω)) =
      s (IsLocalRing.closedPoint Ω) := by
    change s ((Spec.map (CommRingCat.ofHom
      (algebraMap Ω (AlgebraicClosure Ω))))
      (IsLocalRing.closedPoint (AlgebraicClosure Ω))) = _
    congr 1
    exact Subsingleton.elim _ _
  obtain ⟨e, he⟩ := polynomialProjection_affineLine_iso K (n + 1)
  change e.hom ≫ AffineSpace PUnit.{u + 1} B ↘ B = f at he
  let Y := AlgebraicGeometry.ProjectiveLine B
  let g : Y ⟶ B := Y ↘ B
  let j : X ⟶ Y := e.hom ≫ ProjectiveLine.affineChart B
  let i : B ⟶ Y := ProjectiveLine.infinity B
  have hi : IsClosedImmersion i := projectiveLine_infinity_isClosedImmersion B
  have hj : IsOpenImmersion j := inferInstance
  have hij : Set.range i.base = (Set.range j.base)ᶜ := by
    have hr : j.opensRange = (ProjectiveLine.affineChart B).opensRange :=
      Hom.opensRange_comp_of_isIso _ _
    change Set.range i = (j.opensRange : Set Y)ᶜ
    rw [hr]
    exact ProjectiveLine.range_infinity B
  have hig : i ≫ g = 𝟙 B := ProjectiveLine.infinity_over
  have hfg : j ≫ g = f := by
    change (e.hom ≫ ProjectiveLine.affineChart B) ≫ g = f
    rw [Category.assoc, ProjectiveLine.affineChart_over]
    exact he
  have hboundary := isZero_stalk_infinityBoundary_of_lowerDimension K n hIH e M N hN hM
    q hq (AlgebraicClosure Ω) t (by rw [ht]; exact hs)
  have hcolumnStalk := isZero_stalk_lowerStar_of_closedSection i g hig _
    (boundary_support j i hij M q (by omega)) t hboundary
  have hcolumn := isZero_pointPullback_of_algClosure_stalk s _ hcolumnStalk
  have hJM : N • 𝟙 ((Etale.lowerStar AddCommGrpCat.{u + 1} j).obj M) = 0 := by
    have hm := congrArg (Etale.lowerStar AddCommGrpCat.{u + 1} j).map hM
    rw [Functor.map_nsmul, Functor.map_zero] at hm
    rw [(Etale.lowerStar AddCommGrpCat.{u + 1} j).map_id] at hm
    exact hm
  have htotal := isZero_leray_of_row_column j g s M q
    (leray_pullback_zero j g s M q)
    (isZero_rightDerived_projectiveLine_of_killed_by B _ N hN hJM q hq)
    (fun p r hp hr ↦ boundary_mixed_zero j i g hij hig M p r hp hr) hcolumn
  rw [hfg] at htotal
  exact htotal

end AlgebraicGeometry.Scheme
