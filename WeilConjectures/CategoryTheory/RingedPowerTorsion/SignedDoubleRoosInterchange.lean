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
import WeilConjectures.CategoryTheory.RingedPowerTorsion.SignedDoubleRoosChainIso
import WeilConjectures.CategoryTheory.RingedPowerTorsion.SignedDoubleRoosAugmentation

/-! # Signed interchange of two strict Roos limits

Source: Bhatt--Scholze, Lemma 3.4.13; Stacks Tag 0941.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v r

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CochainComplex

namespace CategoryTheory.RingedPowerTorsion

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})

/-- Interchanging the two Roos directions is natural and preserves strict augmentations.
Source: Bhatt--Scholze, Lemma 3.4.13; Stacks Tag 0941
(blueprint: lem-sp-signed-double-roos-interchange).

Proof: In degree k, distribute the two finite biproducts across the countable products.
The four summands are indexed by the two Roos degrees p,q in {0,1}. Reindex the
products by (n,j) ↦ (j,n) and multiply the (p,q) coordinate by (-1)^(p*q).
The same operation twice is the identity. The inner differential is unchanged;
the n differential uses (-1)^((p+1)*q)=(-1)^q*(-1)^(p*q), and the j differential
uses (-1)^(p*(q+1))=(-1)^p*(-1)^(p*q). Thus the maps are chain isomorphisms.
Diagonal product maps commute with reindexing and signs, proving naturality.
Define θ_j by the actual Koszul inclusions in every row, and γ_n by their strict
Roos augmentations. Naturality of tensor inclusions gives natural transformations.
Define etaL as the Roos augmentation of the chain maps Roos(θ_j). Its shifted
coordinate is zero and its unshifted coordinate is their product. To check
etaL followed by interchange equals Roos(γ), project onto all four components.
The nonzero augmentation has second Roos degree zero, so its sign is one;
the other two coordinates are zero. Product and biproduct extensionality finish.
No regularity, torsion or exactness hypothesis is used in this chain calculation.
The chain-level interchange is `signed_double_roos_chain_iso`; the augmentation
comparison for that interchange is `signed_double_roos_augmentation`. -/
theorem signed_double_roos_interchange :
    ∃ T : ∀ V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ,
        doubleLimit R V.flip ≅ doubleLimit R V,
      (∀ V (k : ℤ) (n j : ℕ),
        (T V).hom.f k ≫ doubleCoordinate R V k false false n j =
          doubleCoordinate R V.flip k false false j n ∧
        (T V).hom.f k ≫ doubleCoordinate R V k true false n j =
          doubleCoordinate R V.flip k false true j n ∧
        (T V).hom.f k ≫ doubleCoordinate R V k false true n j =
          doubleCoordinate R V.flip k true false j n ∧
        (T V).hom.f k ≫ doubleCoordinate R V k true true n j =
          -doubleCoordinate R V.flip k true true j n) ∧
      (∀ {V W} (f : V ⟶ W),
        doubleMap R ((flipFunctor _ _ _).map f) ≫ (T W).hom =
          (T V).hom ≫ doubleMap R f) ∧
      (∀ t : (SheafOfModules.unit
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections,
        ∀ U : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ,
          ∃ (γ : U.asFunctor ⟶ koszulDouble R t U ⋙ limitComplex R)
            (θ : ∀ j : ℕ, U.asFunctor ⟶ (koszulDouble R t U).flip.obj (op j))
            (etaL : roosF.obj U ⟶ doubleLimit R (koszulDouble R t U).flip),
            (∀ n, γ.app (op n) = rowUnit R t (U.asFunctor.obj (op n))) ∧
            (∀ (j n : ℕ), (θ j).app (op n) =
              koszulRepresentativeAugmentation R (U.asFunctor.obj (op n)) t j) ∧
            (∀ k : ℤ, etaL.f (k + 1) ≫
              (roosχ (koszulTowerComplex R
                ((koszulDouble R t U).flip ⋙ limitComplex R)) k).hom =
              biprod.lift 0 ((Pi.lift (fun j : ℕ ↦
                roosF.map (koszulTowerComplexMap R (θ j)))).f (k + 1))) ∧
            etaL ≫ (T (koszulDouble R t U)).hom =
              roosF.map (koszulTowerComplexMap R γ)) := by
  obtain ⟨T, hT, hnatural⟩ := signed_double_roos_chain_iso R
  refine ⟨T, hT, hnatural, ?_⟩
  intro t U
  exact signed_double_roos_augmentation R T hT t U

end CategoryTheory.RingedPowerTorsion
