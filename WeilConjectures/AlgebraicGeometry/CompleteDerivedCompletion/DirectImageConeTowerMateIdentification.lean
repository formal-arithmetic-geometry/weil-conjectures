/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageConeTowerNormalizationDefs
import all WeilConjectures.CategoryTheory.AdditiveConeFamilyComparison

/-! Identification of the strict direct-image comparison with the ordinary mate.

Source: literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/prop-weil-pbc-direct-image-limits.proof.md, proof (2).
(blueprint: lem-weil-pbc-direct-image-cone-tower-mate-identification).

The cone inclusions and projections determine the strict comparison. Applying the
ordinary tower and module adjunctions degreewise, the two summand equations identify
its inverse with the mate of the canonical strict pullback/reduction comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived AdicCompletion.finiteRingMonoidalObject
  AdicCompletion.finiteRingCommutative AdicCompletion.finiteModulesDerived

-- A summand equation can be transposed without unfolding the objects it relates.
private theorem counit_summand
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {A B : D} {B' : C}
    (j : A ⟶ B) (h : R.obj B ⟶ B') (k : R.obj A ⟶ B')
    (t : L.obj B' ⟶ B)
    (hh : R.map j ≫ h = k) (ht : L.map k ≫ t = adj.counit.app A ≫ j) :
    L.map (R.map j) ≫ adj.counit.app B = L.map (R.map j) ≫ L.map h ≫ t := by
  calc
    _ = adj.counit.app A ≫ j := adj.counit.naturality j
    _ = L.map k ≫ t := ht.symm
    _ = _ := by rw [← L.map_comp_assoc, hh]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private theorem strictRed_inl_map
    {I J : CochainComplex (AdicCompletion.Modules l E X) ℤ} (g : I ⟶ J) (i : ℤ) :
    (CochainComplex.mappingCone.inl ((complexPowerMap l E X).app I)).v
        (i + 1) i (by omega) ≫ ((strictRed l E X).map g).f i =
      (scalarTower l E X).map (g.f (i + 1)) ≫
        (CochainComplex.mappingCone.inl ((complexPowerMap l E X).app J)).v
          (i + 1) i (by omega) := by
  simp only [strictRed, CochainComplex.mappingCone.map,
    CochainComplex.mappingCone.inl_v_desc_f,
    CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v, Functor.mapHomologicalComplex_map_f]

private theorem strictRed_inr_map
    {I J : CochainComplex (AdicCompletion.Modules l E X) ℤ} (g : I ⟶ J) (i : ℤ) :
    (CochainComplex.mappingCone.inr ((complexPowerMap l E X).app I)).f i ≫
        ((strictRed l E X).map g).f i =
      (constant l E X).map (g.f i) ≫
        (CochainComplex.mappingCone.inr ((complexPowerMap l E X).app J)).f i := by
  simp only [strictRed, CochainComplex.mappingCone.map,
    CochainComplex.mappingCone.inr_f_desc_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f]

set_option maxHeartbeats 1000000 in
-- Evaluating both cone summands requires repeated definitional comparisons of module objects.
/-- The strict cone comparison is the ordinary mate of `strictPullReduction`.
Source: the cone-summand transpose calculation in proof (2) of
`lem-weil-pbc-direct-image-cone-tower-k-injective-normalization`.

The proof checks the shifted and unshifted cone inclusions using `he`, applies
adjunction naturality at every tower level, and concludes by biproduct extensionality.
-/
theorem strictDirectImageConeTower_mate_identification
    (e : strictRed l E X ⋙ (push l E f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      Functor.mapHomologicalComplex
        (CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f)
          (ComplexShape.up ℤ) ⋙ strictRed l E Y)
    (he : IsStrictDirectImageConeTower l E f e) :
    e.inv =
      (mateEquiv
        ((CondensedRing.upperStarLowerStarAdjunction
          (DerivedNakayama.integerRing l E) f).mapHomologicalComplex (.up ℤ))
        (((CondensedRing.upperStarLowerStarAdjunction
          (DerivedNakayama.integerRing l E) f).whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ))
        (TwoSquare.mk _ _ _ _ (strictPullReduction l E f).hom)).natTrans := by
  let adj := CondensedRing.upperStarLowerStarAdjunction
    (DerivedNakayama.integerRing l E) f
  let a := adj.mapHomologicalComplex (.up ℤ)
  let b := (adj.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)
  apply NatTrans.ext
  funext I
  apply (b.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [mateEquiv_counit a b]
  dsimp only [TwoSquare.mk]
  apply (cancel_epi
    (((pull l E f).mapHomologicalComplex (.up ℤ)).map (e.hom.app I))).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hp : IsStrictPullReduction l E f (strictPullReduction l E f) :=
    (strictPullReduction_existsUnique l E f).exists.choose_spec
  apply HomologicalComplex.Hom.ext
  funext i
  apply ConeNaturality.mapCone_ext (push l E f ⋙ pull l E f)
    ((complexPowerMap l E X).app I) i
  · apply NatTrans.ext
    funext n
    rcases n with ⟨n⟩
    let L := CondensedRing.upperStar (DerivedNakayama.integerRing l E) f
    let R := CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f
    let RI := (R.mapHomologicalComplex (.up ℤ)).obj I
    let LI := (L.mapHomologicalComplex (.up ℤ)).obj RI
    let j := ((CochainComplex.mappingCone.inl ((complexPowerMap l E X).app I)).v
      (i + 1) i (by omega)).app (op n)
    let k := ((CochainComplex.mappingCone.inl ((complexPowerMap l E Y).app RI)).v
      (i + 1) i (by omega)).app (op n)
    let z := ((CochainComplex.mappingCone.inl ((complexPowerMap l E X).app LI)).v
      (i + 1) i (by omega)).app (op n)
    let h := ((e.hom.app I).f i).app (op n)
    let p := (((strictPullReduction l E f).hom.app RI).f i).app (op n)
    let q := (((strictRed l E X).map (a.counit.app I)).f i).app (op n)
    have hh : R.map j ≫ h = k := by
      have hh := he.1 I i n
      change _ ≫ _ = 𝟙 _ ≫ _ at hh
      simp only [Category.id_comp] at hh
      change R.map j ≫ h = k at hh
      exact hh
    have hn : z ≫ q = adj.counit.app (I.X (i + 1)) ≫ j := by
      have hn := congr_app (strictRed_inl_map l E (a.counit.app I) i) (op n)
      exact hn
    have hpn : L.map k ≫ p = z := (hp RI i n).1
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.comp_app, Functor.comp_map, b,
      Adjunction.mapHomologicalComplex_counit_app_f,
      Adjunction.whiskerRight_counit_app_app]
    change L.map (R.map j) ≫ adj.counit.app _ =
      L.map (R.map j) ≫ L.map h ≫ (p ≫ q)
    apply counit_summand adj j h k (p ≫ q) hh
    calc
      L.map k ≫ (p ≫ q) = z ≫ q := by rw [← Category.assoc, hpn]
      _ = _ := hn
  · apply NatTrans.ext
    funext n
    rcases n with ⟨n⟩
    let L := CondensedRing.upperStar (DerivedNakayama.integerRing l E) f
    let R := CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f
    let RI := (R.mapHomologicalComplex (.up ℤ)).obj I
    let LI := (L.mapHomologicalComplex (.up ℤ)).obj RI
    let j := ((CochainComplex.mappingCone.inr ((complexPowerMap l E X).app I)).f i).app (op n)
    let k := ((CochainComplex.mappingCone.inr ((complexPowerMap l E Y).app RI)).f i).app (op n)
    let z := ((CochainComplex.mappingCone.inr ((complexPowerMap l E X).app LI)).f i).app (op n)
    let h := ((e.hom.app I).f i).app (op n)
    let p := (((strictPullReduction l E f).hom.app RI).f i).app (op n)
    let q := (((strictRed l E X).map (a.counit.app I)).f i).app (op n)
    have hh : R.map j ≫ h = k := by
      have hh := he.2 I i n
      change _ ≫ _ = 𝟙 _ ≫ _ at hh
      simp only [Category.id_comp] at hh
      change R.map j ≫ h = k at hh
      exact hh
    have hn : z ≫ q = adj.counit.app (I.X i) ≫ j := by
      have hn := congr_app (strictRed_inr_map l E (a.counit.app I) i) (op n)
      exact hn
    have hpn : L.map k ≫ p = z := (hp RI i n).2
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.comp_app, Functor.comp_map, b,
      Adjunction.mapHomologicalComplex_counit_app_f,
      Adjunction.whiskerRight_counit_app_app]
    change L.map (R.map j) ≫ adj.counit.app _ =
      L.map (R.map j) ≫ L.map h ≫ (p ≫ q)
    apply counit_summand adj j h k (p ≫ q) hh
    calc
      L.map k ≫ (p ≫ q) = z ≫ q := by rw [← Category.assoc, hpn]
      _ = _ := hn

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
