/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.PerfectReductionRoos.PerfectReductionRoosData
public import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.PerfectReductionRoos.PerfectReductionKoszulDeltaIso
import WeilConjectures.CategoryTheory.PerfectReductionRoos.PerfectReductionRoosData
import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.TotalTensorSigns.TotalTensorHomotopyConeSigns

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
structure KoszulDeltaData
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (c : CoefficientUnits R t d) where
  δ : ∀ m P, ((total R).obj (principalKoszul R t m)).obj (roosF.obj P) ≅
    roosF.obj (tensorTower R (principalKoszul R t m) P)
  δ_shifted : ∀ m P i p n (h : p + (i + 1) = n + 1) j,
      ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) h ≫
        (δ m P).hom.f (n + 1) ≫
        (roosχ (tensorTower R (principalKoszul R t m) P) n).hom ≫ biprod.fst ≫
        (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t m) P).asFunctor.obj
          (op k)) j).f n =
      p.negOnePow • ((tensor R).obj ((principalKoszul R t m).X p)).map
        ((roosχ P i).hom ≫ biprod.fst ≫
          (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) j).f i) ≫
        ι R (principalKoszul R t m) (P.asFunctor.obj (op j)) p i n (by omega)
  δ_unshifted : ∀ m P i p n (h : p + (i + 1) = n + 1) j,
      ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) h ≫
        (δ m P).hom.f (n + 1) ≫
        (roosχ (tensorTower R (principalKoszul R t m) P) n).hom ≫ biprod.snd ≫
        (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t m) P).asFunctor.obj
          (op k)) j).f (n + 1) =
      ((tensor R).obj ((principalKoszul R t m).X p)).map
        ((roosχ P i).hom ≫ biprod.snd ≫
          (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) j).f (i + 1)) ≫
        ι R (principalKoszul R t m) (P.asFunctor.obj (op j)) p (i + 1) (n + 1) h
/-- Strict signed finite tensor/Roos comparison data; source Bhatt--Scholze Lemma 3.5.5.

Proof: The finite tensor-cone comparison is distributed through the countable Roos
product and its biproduct. The shifted product receives the sign (-1)^p and the
unshifted product receives sign one. Product and biproduct extensionality prove the
chain map and inverse equations, and the same coordinate calculation gives both
displayed identities.
(blueprint: lem-sp-perfect-reduction-koszul-comparison-delta-data). -/
theorem nonempty_koszulDeltaData
    (ht : Mono (globalSectionMultiplication R t))
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (c : CoefficientUnits R t d) : Nonempty (KoszulDeltaData R t d c) := by
  obtain ⟨r⟩ := nonempty_koszulDeltaRawData R t ht d c
  obtain ⟨e⟩ := nonempty_koszulDeltaIso R t ht d c r
  let δ : ∀ m P, ((total R).obj (principalKoszul R t m)).obj (roosF.obj P) ≅
      roosF.obj (tensorTower R (principalKoszul R t m) P) := fun m P ↦ (e m P).1
  refine ⟨{ δ := δ, δ_shifted := ?_, δ_unshifted := ?_ }⟩
  · intro m P i p n h j
    simpa only [δ, (e m P).2] using r.shifted m P i p n h j
  · intro m P i p n h j
    simpa only [δ, (e m P).2] using r.unshifted m P i p n h j
end CategoryTheory.PerfectReductionRoos
