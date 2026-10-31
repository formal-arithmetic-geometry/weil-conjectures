/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PerfectReductionCoefficientUnits

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
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
structure KoszulTransitionData
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (c : CoefficientUnits R t d)
    (δ : ∀ m P, ((total R).obj (principalKoszul R t m)).obj (roosF.obj P) ≅
      roosF.obj (tensorTower R (principalKoszul R t m) P)) where
  koszul_changes : ∀ l m (h : l ≤ m) P,
      ((total R).map
        ((principalKoszulTower R t).map (homOfLE h).op)).app (roosF.obj P) ≫ (δ l P).hom =
        (δ m P).hom ≫ roosF.map
          (tensorTowerMap R ((principalKoszulTower R t).map (homOfLE h).op) P)

/-- transition compatibility data; source Bhatt--Scholze Lemma 3.5.5.

Proof: The principal transition has the explicit two components (t^(m-l),1). Naturality of
the signed tensor/product distribution makes the two composites agree on every shifted
and unshifted Roos coordinate. Product and biproduct extensionality then give the
required chain-map equality.
(blueprint: lem-sp-perfect-reduction-koszul-comparison-transition-data). -/
theorem nonempty_koszulTransitionData
    (ht : Mono (globalSectionMultiplication R t))
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (c : CoefficientUnits R t d)
    (δ : ∀ m P, ((total R).obj (principalKoszul R t m)).obj (roosF.obj P) ≅
      roosF.obj (tensorTower R (principalKoszul R t m) P))
    (hδ_shifted : ∀ m P i p n (h : p + (i + 1) = n + 1) j,
      ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) h ≫
        (δ m P).hom.f (n + 1) ≫
        (roosχ (tensorTower R (principalKoszul R t m) P) n).hom ≫ biprod.fst ≫
        (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t m) P).asFunctor.obj
          (op k)) j).f n =
      p.negOnePow • ((tensor R).obj ((principalKoszul R t m).X p)).map
        ((roosχ P i).hom ≫ biprod.fst ≫
          (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) j).f i) ≫
        ι R (principalKoszul R t m) (P.asFunctor.obj (op j)) p i n (by omega))
    (hδ_unshifted : ∀ m P i p n (h : p + (i + 1) = n + 1) j,
      ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) h ≫
        (δ m P).hom.f (n + 1) ≫
        (roosχ (tensorTower R (principalKoszul R t m) P) n).hom ≫ biprod.snd ≫
        (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t m) P).asFunctor.obj
          (op k)) j).f (n + 1) =
      ((tensor R).obj ((principalKoszul R t m).X p)).map
        ((roosχ P i).hom ≫ biprod.snd ≫
          (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) j).f (i + 1)) ≫
        ι R (principalKoszul R t m) (P.asFunctor.obj (op j)) p (i + 1) (n + 1) h) :
    Nonempty (KoszulTransitionData R t d c δ) := by
  sorry
end CategoryTheory.PerfectReductionRoos
