/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionModel
public import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeBasic
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
/-! # Fixed representatives for principal torsion completion

The strict Roos, double-Roos and Koszul constructions used by the canonical
power-torsion completeness argument. These definitions are extracted verbatim
from the original statement module to permit independent proofs of its steps.
Source: Bhatt--Scholze, Section 3.4 and Lemma 3.5.7.
(blueprint: def-sp-ringed-power-torsion-limit-models).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.RingedPowerTorsion

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})

/-- The existing strict Roos functor on a tower presented as a functor to complexes.
Source: Bhatt--Scholze, Section 3.4; Stacks 0941
(blueprint: def-sp-ringed-power-torsion-limit-models). -/
def limitComplex := PrincipalQuotientCompletion.transpose R ⋙ roosF

/-- Apply the fixed Roos model first to the inner and then to the outer index.
Source: Bhatt--Scholze, Lemma 3.4.13, double-limit calculation
(blueprint: def-sp-ringed-power-torsion-limit-models). -/
def doubleLimit (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ) :=
  (limitComplex R).obj (V ⋙ limitComplex R)

/-- The induced map on both strict Roos directions.
Source: Bhatt--Scholze, Lemma 3.4.13
(blueprint: def-sp-ringed-power-torsion-limit-models). -/
def doubleMap {V W : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ}
    (f : V ⟶ W) : doubleLimit R V ⟶ doubleLimit R W :=
  (limitComplex R).map (Functor.whiskerRight f (limitComplex R))

/-- The internal degree after selecting an unshifted or shifted Roos coordinate.
Source: Bhatt--Scholze, Lemma 3.4.13, two Roos degrees
(blueprint: def-sp-ringed-power-torsion-limit-models). -/
def degree (k : ℤ) (shifted : Bool) : ℤ := if shifted then k - 1 else k

/-- The actual two Roos projections, before taking a product projection.
Source: Stacks 0941; Bhatt--Scholze, Lemma 3.4.13
(blueprint: def-sp-ringed-power-torsion-limit-models). -/
def coordinate (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ) (k : ℤ) :
    (b : Bool) → (roosF.obj X).X k ⟶ (roosP X).X (degree k b)
  | false => (CochainComplex.mappingCocone.fst (roosU X)).f k
  | true => (CochainComplex.mappingCocone.snd (roosU X)).v k (k - 1) (by omega)

/-- A component of the iterated Roos product in its two Roos degrees.
Source: Bhatt--Scholze, Lemma 3.4.13, explicit product transposition
(blueprint: def-sp-ringed-power-torsion-limit-models). -/
def doubleCoordinate (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
    (k : ℤ) (p q : Bool) (n j : ℕ) :
    (doubleLimit R V).X k ⟶ ((V.obj (op n)).obj (op j)).X (degree (degree k p) q) :=
  coordinate R (koszulTowerComplex R (V ⋙ limitComplex R)) k p ≫
    (Pi.π (fun n : ℕ ↦ (limitComplex R).obj (V.obj (op n))) n).f (degree k p) ≫
    coordinate R (koszulTowerComplex R (V.obj (op n))) (degree k p) q ≫
    (Pi.π (fun j : ℕ ↦ (V.obj (op n)).obj (op j)) j).f (degree (degree k p) q)

/-- The existing tensor Koszul tower, functorial in the input complex. This is the
native curried-tensor spelling used by the quotient completion model.
Source: Bhatt--Scholze, Lemma 3.4.9
(blueprint: def-sp-ringed-power-torsion-limit-models). -/
def koszulRows
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections) :
    CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ ⥤
      ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  exact (curriedTensor (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))).map₂CochainComplex.flip ⋙
    (Functor.whiskeringLeft ℕᵒᵖ _ _).obj (principalKoszulTower R t)

/-- The raw strict Koszul double tower, with no replacement of the torsion rows.
Source: Bhatt--Scholze, Lemmas 3.4.9 and 3.4.13
(blueprint: def-sp-ringed-power-torsion-limit-models). -/
def koszulDouble
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (U : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ) :=
  U.asFunctor ⋙ koszulRows R t

/-- The Koszul Roos completion before localization.
Source: Bhatt--Scholze, Lemma 3.4.9
(blueprint: def-sp-ringed-power-torsion-limit-models). -/
def koszulCompletion
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections) :=
  koszulRows R t ⋙ limitComplex R

/-- The actual map to ordinary quotient completion, induced by K_j → R/t^(j+1).
Its localization is invertible on K-flat inputs for regular t.
Source: Bhatt--Scholze, Lemma 3.4.9; Stacks 06YT and 0941
(blueprint: def-sp-ringed-power-torsion-limit-models). -/
def quotientComparison
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (P : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ) :
    (koszulCompletion R t).obj P ⟶ (PrincipalQuotientCompletion.quotientRoos R t).obj P :=
  (limitComplex R).map (koszulTensorTowerComparison R P t)

/-- Coordinate characterization of finite-Koszul distribution across the strict Roos cone.
On K_j^i tensor the Roos-degree-q coordinate it is the product projection with
sign (-1)^(i*q). Quantifying over all tensor inclusions and both Roos coordinates
fixes the entire chain map, including its shifted coordinate, independently of units.
Source: Bhatt--Scholze, Lemma 3.5.5, perfect-complex comparison a
(blueprint: def-sp-ringed-power-torsion-limit-models). -/
def distributionCoordinates
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (U : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
    (D : (koszulRows R t).obj (roosF.obj U) ≅
      (koszulDouble R t U).flip ⋙ limitComplex R) : Prop := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  exact ∀ (j n : ℕ) (i a k : ℤ) (h : i + a = k) (q : Bool),
    CochainComplex.ιMapBifunctor (principalKoszul R t j) (roosF.obj U)
        (curriedTensor _) i a k h ≫ (D.hom.app (op j)).f k ≫
      coordinate R (koszulTowerComplex R ((koszulDouble R t U).flip.obj (op j))) k q ≫
      (Pi.π (fun n : ℕ ↦ ((koszulDouble R t U).obj (op n)).obj (op j)) n).f
        (degree k q) =
    (if q then (i.negOnePow : ℤ) else (1 : ℤ)) •
      (((curriedTensor _).obj ((principalKoszul R t j).X i)).map
          (coordinate R U a q ≫
            (Pi.π (fun n : ℕ ↦ U.asFunctor.obj (op n)) n).f (degree a q)) ≫
        CochainComplex.ιMapBifunctor (principalKoszul R t j) (U.asFunctor.obj (op n))
          (curriedTensor _) i (degree a q) (degree k q)
          (by cases q <;> simp [degree] <;> omega))

/-- The actual row unit: the strict Koszul inclusions and zero shifted-product coordinate.
Source: Bhatt--Scholze, Lemma 3.4.9; Stacks 0941
(blueprint: def-sp-ringed-power-torsion-limit-models). -/
def rowUnit
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (P : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ) :
    P ⟶ (limitComplex R).obj (koszulTensorTower R P t) :=
  roosAugment (koszulRepresentativeAugmentation R P t)
    (fun j ↦ (koszulRepresentativeAugmentation_naturality R P t j).symm)

end CategoryTheory.RingedPowerTorsion
