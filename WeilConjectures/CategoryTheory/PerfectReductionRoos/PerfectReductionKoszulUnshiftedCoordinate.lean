/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.PerfectReductionRoos.PerfectReductionRoosData

/-! # The unshifted Roos coordinate of the Koszul transition

Source: Bhatt--Scholze, Lemma 3.5.5, coordinate calculation for the strict signed
perfect-complex comparison (blueprint: lem-sp-perfect-reduction-koszul-unshifted-coordinate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r wR wA
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.RegularQuotientCone SheafOfModules.TotalTensorSigns
open scoped ChangeOfRings
namespace CategoryTheory.PerfectReductionRoos
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}]
  (R : Sheaf J CommRingCat.{r})
  (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
variable [HasDerivedCategory.{wR} (RegularQuotientCone.Modules R)]
  [∀ m, HasDerivedCategory.{wA} (RegularQuotientCone.Modules (powerRing R t m))]
  [HasDerivedCategory.{wR} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R)]
  [∀ m, HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules (powerRing R t m))]
  [HasCountableProducts (RegularQuotientCone.Modules R)]
  [∀ m, HasCountableProducts (RegularQuotientCone.Modules (powerRing R t m))]

/-- A single unshifted Roos coordinate of transition compatibility.

Source: Bhatt--Scholze, Lemma 3.5.5, strict signed perfect-complex comparison a.

Proof: on the summand `K_m^p ⊗ (Roos P)^(i+1)` the total-tensor map of the transition
`φ : K_m ⟶ K_l` is `φ^p ⊗ 1` followed by the summand inclusion for `K_l`
(`ι_mapBifunctorMap`). The given coordinate formula for `δ` at `l` and at `m` rewrites
both sides through the second (unshifted) biproduct component, in degree n+1,
of the Roos product; the product map of `tensorTowerMap φ P` followed by the `j`-th
projection is the `j`-th projection followed by the total-tensor map of `φ` on the `j`-th
level (`Pi.map_π`), which is again `φ^p ⊗ 1` on the summand. The two sides then agree by
naturality of `φ^p ⊗ -`; no sign occurs.
(blueprint: lem-sp-perfect-reduction-koszul-unshifted-coordinate). -/
theorem koszul_transition_unshifted_coordinate
    (δ : ∀ m P, ((total R).obj (principalKoszul R t m)).obj (roosF.obj P) ≅
      roosF.obj (tensorTower R (principalKoszul R t m) P))
    (hδ_unshifted : ∀ m P i p n (h : p + (i + 1) = n + 1) j,
      ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) h ≫
        (δ m P).hom.f (n + 1) ≫
        (roosχ (tensorTower R (principalKoszul R t m) P) n).hom ≫ biprod.snd ≫
        (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t m) P).asFunctor.obj
          (op k)) j).f (n + 1) =
      ((tensor R).obj ((principalKoszul R t m).X p)).map
        ((roosχ P i).hom ≫ biprod.snd ≫
          (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) j).f (i + 1)) ≫
        ι R (principalKoszul R t m) (P.asFunctor.obj (op j)) p (i + 1) (n + 1) (by omega))
    (l m : ℕ) (h : l ≤ m) (P : CochainComplex (ℕᵒᵖ ⥤ TotalTensorSigns.Modules R) ℤ)
    (n p i : ℤ)
    (hpq : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (p, (Equiv.addRight 1) i) = n + 1)
    (hpq' : p + (i + 1) = n + 1)
    (j : ℕ) :
    HomologicalComplex.ιMapBifunctor (principalKoszul R t m) (roosF.obj P)
      (tensor R) (ComplexShape.up ℤ) p ((Equiv.addRight 1) i) (n + 1) hpq ≫
        (((total R).map ((principalKoszulTower R t).map (homOfLE h).op)).app
          (roosF.obj P)).f (n + 1) ≫
        (δ l P).hom.f (n + 1) ≫
        (roosχ (tensorTower R (principalKoszul R t l) P) n).hom ≫ biprod.snd ≫
        (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t l) P).asFunctor.obj
          (op k)) j).f (n + 1) =
      HomologicalComplex.ιMapBifunctor (principalKoszul R t m) (roosF.obj P)
        (tensor R) (ComplexShape.up ℤ) p ((Equiv.addRight 1) i) (n + 1) hpq ≫
        (δ m P).hom.f (n + 1) ≫
        (roosχ (tensorTower R (principalKoszul R t m) P) n).hom ≫ biprod.snd ≫
        (roosPmap (tensorTowerMap R ((principalKoszulTower R t).map
          (homOfLE h).op) P)).f (n + 1) ≫
        (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t l) P).asFunctor.obj
          (op k)) j).f (n + 1) := by
  set φ := (principalKoszulTower R t).map (homOfLE h).op
  suffices key : ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) hpq' ≫
        (((total R).map φ).app (roosF.obj P)).f (n + 1) ≫
        (δ l P).hom.f (n + 1) ≫
        (roosχ (tensorTower R (principalKoszul R t l) P) n).hom ≫ biprod.snd ≫
        (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t l) P).asFunctor.obj
          (op k)) j).f (n + 1) =
      ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) hpq' ≫
        (δ m P).hom.f (n + 1) ≫
        (roosχ (tensorTower R (principalKoszul R t m) P) n).hom ≫ biprod.snd ≫
        (roosPmap (tensorTowerMap R φ P)).f (n + 1) ≫
        (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t l) P).asFunctor.obj
          (op k)) j).f (n + 1) by
    exact key
  have e1 : ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) hpq' ≫
        (((total R).map φ).app (roosF.obj P)).f (n + 1) =
      ((tensor R).map (φ.f p)).app ((roosF.obj P).X (i + 1)) ≫
        ι R (principalKoszul R t l) (roosF.obj P) p (i + 1) (n + 1) hpq' := by
    dsimp only [total, Functor.map₂CochainComplex, Functor.map₂HomologicalComplex, ι]
    rw [HomologicalComplex.ι_mapBifunctorMap]
    simp
    rfl
  have e2 : ι R (principalKoszul R t m) (P.asFunctor.obj (op j)) p (i + 1) (n + 1) hpq' ≫
      (((total R).map φ).app (P.asFunctor.obj (op j))).f (n + 1) =
      ((tensor R).map (φ.f p)).app ((P.asFunctor.obj (op j)).X (i + 1)) ≫
        ι R (principalKoszul R t l) (P.asFunctor.obj (op j)) p (i + 1) (n + 1) hpq' := by
    dsimp only [total, Functor.map₂CochainComplex, Functor.map₂HomologicalComplex, ι]
    rw [HomologicalComplex.ι_mapBifunctorMap]
    simp
    rfl
  have e3 : (roosPmap (tensorTowerMap R φ P)).f (n + 1) ≫
      (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t l) P).asFunctor.obj
          (op k)) j).f (n + 1) =
      (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t m) P).asFunctor.obj
          (op k)) j).f (n + 1) ≫
        (((total R).map φ).app (P.asFunctor.obj (op j))).f (n + 1) := by
    rw [← HomologicalComplex.comp_f]
    have hπ := Pi.map_π (fun k : ℕ ↦
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        (tensorTowerMap R φ P)).app (op k)) j
    exact congrArg (fun g ↦ HomologicalComplex.Hom.f g (n + 1)) hπ
  rw [reassoc_of% e1, hδ_unshifted l P i p n hpq' j, e3,
    reassoc_of% hδ_unshifted m P i p n hpq' j, e2]
  exact (((tensor R).map (φ.f p)).naturality_assoc _ _).symm
end CategoryTheory.PerfectReductionRoos
