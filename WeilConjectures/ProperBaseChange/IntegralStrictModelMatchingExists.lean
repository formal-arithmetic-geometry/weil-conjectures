/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.ProperIntegralOrdinaryData
import WeilConjectures.ProperBaseChange.IntegralStrictModelChainTransport
import WeilConjectures.ProperBaseChange.IntegralStrictRoosResolution
import WeilConjectures.ProperBaseChange.IntegralActualTowerComputation
import WeilConjectures.ProperBaseChange.IntegralCoefficientRoosCoordinates
import WeilConjectures.ProperBaseChange.IntegralGoodModelComparison
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Strict tower model comparison before completion units

Given an ordinary pullback identification `a`, the integral derived pullback followed by
detailed transport is identified with the completed reduction tower, pulled back and followed
by the derived limit, by a natural isomorphism `b` satisfying the model-matching equations
`PbcProperIntegralModelMatching l E h a b`.

## Main results

* `WeilConjectures.pbc_integral_strict_model_matching_exists`

## Implementation details

On a flat-term K-flat representative `P`, balancing scalar tensors with each finite quotient
identifies the actual pulled reduction tower with the ordinary finite-pullback tower; these
identifications form an isomorphism `t` of strict towers, and the `module_unit` condition on `a`
gives the augmentation equation. Transporting the mapping cocone of `1 - s` through the product
comparisons gives `z`, whose two coordinates give the Roos coordinate equations. The actual
tower counit is invertible because the completed coefficient inverse-image map is an
isomorphism, so ordinary module pullback and its levelwise tower functor are exact. For a
K-injective resolution with injective tower terms, `1 - s` is degreewise epic with kernel the
ordinary limit, and the inclusion of this kernel into the mapping cocone is a
quasi-isomorphism; naturality of the universal derived-limit unit gives the formula for every
resolution. The resulting natural isomorphism on good representatives descends along the
good-complex localization to `b`.

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 6.5.9(4), Remark 6.8.15.
* Stacks Project, Tags 0941 and 099N(5).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] integralDerivedPullback completedReductionTower pbcIntegralDatum
  integralDetailedCoefficientComparison Functor.mapDerivedCategory HasDerivedCategory.standard

section Helpers

@[reassoc]
private theorem functor_map_inv_cancel
    {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)
    {X Y Z : A} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) :
    F.map (inv f) ≫ F.map (f ≫ g) = F.map g := by
  rw [← F.map_comp, IsIso.inv_hom_id_assoc]

private def rightAssoc3
    {A B C D E : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]
    (F0 : A ⥤ B)
    (F1 : B ⥤ C)
    (F2 : C ⥤ D)
    (F3 : D ⥤ E) :
    (F0 ⋙ F1 ⋙ F2) ⋙ F3 ≅ F0 ⋙ F1 ⋙ F2 ⋙ F3 :=
  Functor.associator F0 (F1 ⋙ F2) F3 ≪≫
    Functor.isoWhiskerLeft F0 (Functor.associator F1 F2 F3)

@[simp]
private theorem rightAssoc3_hom_app
    {A B C D E : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]
    (F0 : A ⥤ B)
    (F1 : B ⥤ C)
    (F2 : C ⥤ D)
    (F3 : D ⥤ E) (X : A) :
    (rightAssoc3 F0 F1 F2 F3).hom.app X = 𝟙 _ := by
  simp [rightAssoc3]

@[simp]
private theorem rightAssoc3_inv_app
    {A B C D E : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]
    (F0 : A ⥤ B)
    (F1 : B ⥤ C)
    (F2 : C ⥤ D)
    (F3 : D ⥤ E) (X : A) :
    (rightAssoc3 F0 F1 F2 F3).inv.app X = 𝟙 _ := by
  simp [rightAssoc3]

private def rightAssoc4
    {A B C D E F : Type*}
    [Category* A]
    [Category* B]
    [Category* C]
    [Category* D]
    [Category* E]
    [Category* F]
    (F0 : A ⥤ B)
    (F1 : B ⥤ C)
    (F2 : C ⥤ D)
    (F3 : D ⥤ E)
    (F4 : E ⥤ F) :
    (F0 ⋙ F1 ⋙ F2 ⋙ F3) ⋙ F4 ≅ F0 ⋙ F1 ⋙ F2 ⋙ F3 ⋙ F4 :=
  Functor.associator F0 (F1 ⋙ F2 ⋙ F3) F4 ≪≫
    Functor.isoWhiskerLeft F0 (rightAssoc3 F1 F2 F3 F4)

@[simp]
private theorem rightAssoc4_hom_app
    {A B C D E F : Type*}
    [Category* A]
    [Category* B]
    [Category* C]
    [Category* D]
    [Category* E]
    [Category* F]
    (F0 : A ⥤ B)
    (F1 : B ⥤ C)
    (F2 : C ⥤ D)
    (F3 : D ⥤ E)
    (F4 : E ⥤ F) (X : A) :
    (rightAssoc4 F0 F1 F2 F3 F4).hom.app X = 𝟙 _ := by
  simp [rightAssoc4]

@[simp]
private theorem rightAssoc4_inv_app
    {A B C D E F : Type*}
    [Category* A]
    [Category* B]
    [Category* C]
    [Category* D]
    [Category* E]
    [Category* F]
    (F0 : A ⥤ B)
    (F1 : B ⥤ C)
    (F2 : C ⥤ D)
    (F3 : D ⥤ E)
    (F4 : E ⥤ F) (X : A) :
    (rightAssoc4 F0 F1 F2 F3 F4).inv.app X = 𝟙 _ := by
  simp [rightAssoc4]

private def rightAssoc5
    {A B C D E F G : Type*}
    [Category* A]
    [Category* B]
    [Category* C]
    [Category* D]
    [Category* E]
    [Category* F]
    [Category* G]
    (F0 : A ⥤ B)
    (F1 : B ⥤ C)
    (F2 : C ⥤ D)
    (F3 : D ⥤ E)
    (F4 : E ⥤ F)
    (F5 : F ⥤ G) :
    (F0 ⋙ F1 ⋙ F2 ⋙ F3 ⋙ F4) ⋙ F5 ≅ F0 ⋙ F1 ⋙ F2 ⋙ F3 ⋙ F4 ⋙ F5 :=
  Functor.associator F0 (F1 ⋙ F2 ⋙ F3 ⋙ F4) F5 ≪≫
    Functor.isoWhiskerLeft F0 (rightAssoc4 F1 F2 F3 F4 F5)

@[simp]
private theorem rightAssoc5_hom_app
    {A B C D E F G : Type*}
    [Category* A]
    [Category* B]
    [Category* C]
    [Category* D]
    [Category* E]
    [Category* F]
    [Category* G]
    (F0 : A ⥤ B)
    (F1 : B ⥤ C)
    (F2 : C ⥤ D)
    (F3 : D ⥤ E)
    (F4 : E ⥤ F)
    (F5 : F ⥤ G) (X : A) :
    (rightAssoc5 F0 F1 F2 F3 F4 F5).hom.app X = 𝟙 _ := by
  simp [rightAssoc5]

private def normalizedWhisker3
    {A B C D E G : Type*}
    [Category* A]
    [Category* B]
    [Category* C]
    [Category* D]
    [Category* E]
    [Category* G]
    {F0 : A ⥤ B} {F1 : B ⥤ C} {F2 : C ⥤ E}
    {G1 : B ⥤ D} {G2 : D ⥤ E}
    (α : F0 ⋙ F1 ⋙ F2 ≅ F0 ⋙ G1 ⋙ G2) (H : E ⥤ G) :
    F0 ⋙ F1 ⋙ F2 ⋙ H ≅ F0 ⋙ G1 ⋙ G2 ⋙ H :=
  (rightAssoc3 F0 F1 F2 H).symm ≪≫
    Functor.isoWhiskerRight α H ≪≫ rightAssoc3 F0 G1 G2 H

@[simp]
private theorem normalizedWhisker3_hom_app
    {A B C D E G : Type*}
    [Category* A]
    [Category* B]
    [Category* C]
    [Category* D]
    [Category* E]
    [Category* G]
    {F0 : A ⥤ B} {F1 : B ⥤ C} {F2 : C ⥤ E}
    {G1 : B ⥤ D} {G2 : D ⥤ E}
    (α : F0 ⋙ F1 ⋙ F2 ≅ F0 ⋙ G1 ⋙ G2) (H : E ⥤ G) (X : A) :
    (normalizedWhisker3 α H).hom.app X = H.map (α.hom.app X) := by
  simp [normalizedWhisker3]

private def normalizedWhisker4
    {A B C C₁ D D₁ E G : Type*}
    [Category* A]
    [Category* B]
    [Category* C]
    [Category* C₁]
    [Category* D]
    [Category* D₁]
    [Category* E]
    [Category* G]
    {F0 : A ⥤ B} {F1 : B ⥤ C} {F2 : C ⥤ D} {F3 : D ⥤ E}
    {G1 : B ⥤ C₁} {G2 : C₁ ⥤ D₁} {G3 : D₁ ⥤ E}
    (α : F0 ⋙ F1 ⋙ F2 ⋙ F3 ≅ F0 ⋙ G1 ⋙ G2 ⋙ G3) (H : E ⥤ G) :
    F0 ⋙ F1 ⋙ F2 ⋙ F3 ⋙ H ≅ F0 ⋙ G1 ⋙ G2 ⋙ G3 ⋙ H :=
  (rightAssoc4 F0 F1 F2 F3 H).symm ≪≫
    Functor.isoWhiskerRight α H ≪≫ rightAssoc4 F0 G1 G2 G3 H

@[simp]
private theorem normalizedWhisker4_hom_app
    {A B C C₁ D D₁ E G : Type*}
    [Category* A]
    [Category* B]
    [Category* C]
    [Category* C₁]
    [Category* D]
    [Category* D₁]
    [Category* E]
    [Category* G]
    {F0 : A ⥤ B} {F1 : B ⥤ C} {F2 : C ⥤ D} {F3 : D ⥤ E}
    {G1 : B ⥤ C₁} {G2 : C₁ ⥤ D₁} {G3 : D₁ ⥤ E}
    (α : F0 ⋙ F1 ⋙ F2 ⋙ F3 ≅ F0 ⋙ G1 ⋙ G2 ⋙ G3) (H : E ⥤ G) (X : A) :
    (normalizedWhisker4 α H).hom.app X = H.map (α.hom.app X) := by
  simp [normalizedWhisker4]

private theorem iso_preimage_exists
    {C D : Type*} [Category* C] [Category* D] {K : C ⥤ D}
    (hK : K.FullyFaithful) {X Y : C} (e : K.obj X ≅ K.obj Y) :
    ∃ b : X ≅ Y, K.map b.hom = e.hom := by
  exact ⟨hK.preimageIso e, hK.map_preimage e.hom⟩

end Helpers

attribute [local irreducible] integralOperationsRoos integralDerivedPullbackComparison
  pbcIntegralDetailedTransportFactors

/-- The completed functors have a comparison normalized independently of their
completion maps. Its equations specify the strict tower, both Roos coordinates,
and its value after every entire-tower K-injective resolution: for every pullback
identification `a` there is a natural isomorphism `b` with
`PbcProperIntegralModelMatching l E h a b`. -/
theorem pbc_integral_strict_model_matching_exists
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {U T : Scheme.{u}} (h : U ⟶ T)
    (a : PbcProperIntegralPullbackIdentification l E h) :
    ∃ b : integralDerivedPullback l E h ⋙ integralDetailedTransport U l E ≅
        integralDetailedTransport T l E ⋙ completedReductionTower T (pbcIntegralDatum l E) ⋙
          completedTowerPullback h (pbcIntegralDatum l E) ⋙
            completedTowerRlim (pbcIntegralDatum l E) U,
      PbcProperIntegralModelMatching l E h a b := by
  classical
  obtain ⟨t, ht⟩ := pbc_integral_strict_model_chain_transport l E h a
  obtain ⟨he, hCounit, c₀, hc₀⟩ := pbc_integral_actual_tower_computation l E h
  let := he
  obtain ⟨γ, hγ⟩ := pbc_integral_coefficient_roos_coordinates l E U
  let J := (integralOperationsGoodComplex l E T).ι
  let z := Functor.isoWhiskerLeft J
      (Functor.isoWhiskerLeft (integralOperationsPullbackTowerFunctor l E h)
        γ) ≪≫
    normalizedWhisker3 (F0 := J) t.symm integralOperationsRoosFunctor
  have hz (P : (integralOperationsGoodComplex l E T).FullSubcategory) :
      z.hom.app P = γ.hom.app
          ((integralOperationsPullbackTowerFunctor l E h).obj P.obj) ≫
        integralOperationsRoosFunctor.map (t.inv.app P) := by
    simp only [z, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, normalizedWhisker3_hom_app, Iso.symm_hom]
    rfl
  obtain ⟨ρ, hρ⟩ := pbc_integral_strict_roos_resolution (pbcIntegralDatum l E) U
  let L := integralOperationsGoodLocalization l E T
  let R := completedTowerRlim (pbcIntegralDatum l E) U
  let F := integralDerivedPullback l E h ⋙ integralDetailedTransport U l E
  let G := integralDetailedTransport T l E ⋙
    completedReductionTower T (pbcIntegralDatum l E) ⋙
      completedTowerPullback h (pbcIntegralDatum l E) ⋙ R
  let c := Functor.whiskerLeft J c₀
  have hc (P : (integralOperationsGoodComplex l E T).FullSubcategory) :
      c.app P = pbcIntegralActualTowerCounit l E h P.obj := hc₀ P.obj
  have (P : (integralOperationsGoodComplex l E T).FullSubcategory) :
      IsIso (c.app P) := by rw [hc]; exact hCounit P
  have : IsIso c := NatIso.isIso_of_isIso_app c
  obtain ⟨e₀, he₀⟩ := pbc_integral_good_model_comparison l E h
  let ez := Functor.isoWhiskerLeft J
      (Functor.associator (integralOperationsPullbackTowerFunctor l E h)
        integralOperationsRoosFunctor (pbcIntegralTransportComplex U l E ⋙ DerivedCategory.Q)) ≪≫
    normalizedWhisker4 (F0 := J) z DerivedCategory.Q
  let erho := Functor.isoWhiskerLeft J
    (Functor.isoWhiskerLeft (pbcIntegralActualTowerFunctor l E h) ρ)
  let ec := (rightAssoc3 J (pbcIntegralActualTowerFunctor l E h) DerivedCategory.Q R).symm ≪≫
    (Functor.isoWhiskerRight (asIso c) R).symm ≪≫
    rightAssoc5 J DerivedCategory.Q (integralDetailedTransport T l E)
      (completedReductionTower T (pbcIntegralDatum l E))
      (completedTowerPullback h (pbcIntegralDatum l E)) R ≪≫
    (Functor.associator J DerivedCategory.Q G).symm
  let e : L ⋙ F ≅ L ⋙ G := e₀ ≪≫ ez ≪≫ erho ≪≫ ec
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E T) (.up ℤ)).inverseImage J
  let := integralOperationsGoodLocalization_isLocalization l E T
  let ff := Localization.fullyFaithfulWhiskeringLeft L W
    (PbcCompletedDerived U (pbcIntegralDatum l E))
  obtain ⟨b, hb₀⟩ := iso_preimage_exists ff e
  have hb (P : (integralOperationsGoodComplex l E T).FullSubcategory) :
      b.hom.app (DerivedCategory.Q.obj P.obj) = e.hom.app P :=
    NatTrans.congr_app hb₀ P
  refine ⟨b, ?_⟩
  intro P
  refine ⟨hCounit P, t.app P, z.app P, ht P, ?_, ?_⟩
  · exact hγ
      (pbcIntegralActualTower l E h P.obj).asFunctor
      ((integralOperationsPullbackTowerFunctor l E h).obj P.obj)
      (t.app P) (z.app P) (hz P)
  · intro I r hqr hki hi
    have hr := @hρ (pbcIntegralActualTower l E h P.obj) I r hqr hki hi
    obtain ⟨ι, hι₁, hι₂, hι₃⟩ := hr
    refine ⟨ι, hι₁, hι₂, ?_⟩
    rw [hb]
    simp only [e, ez, erho, ec, Iso.app_hom,
      rightAssoc3_inv_app, rightAssoc5_hom_app, normalizedWhisker4_hom_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_inv,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      asIso_inv, NatIso.isIso_inv_app, Category.assoc]
    rw [← hc]
    erw [Category.id_comp, Category.id_comp, Category.id_comp]
    erw [functor_map_inv_cancel_assoc]
    calc
      _ = e₀.hom.app P ≫ DerivedCategory.Q.map (z.hom.app P) ≫
          DerivedCategory.Q.map (integralOperationsRoosFunctor.map
            (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map r)) := by
        exact congrArg (fun f ↦ e₀.hom.app P ≫ DerivedCategory.Q.map (z.hom.app P) ≫ f) hι₃
      _ = _ := by
        simp only [he₀, Category.assoc]

end WeilConjectures
