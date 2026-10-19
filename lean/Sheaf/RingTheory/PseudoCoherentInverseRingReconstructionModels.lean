/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.Algebra.Homology.DerivedChangeOfRings
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Sheaf.RingTheory.PseudoCoherentNilpotentInvariance
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Sheaf.Algebra.Homology.SurjectiveModuleComplexTowerLimit
import Sheaf.RingTheory.NilpotentMarkedFreeComplexLift
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction

/-!
# Pseudo-coherent reconstruction over a tower of nilpotent quotients

Source: Stacks Project, More on Algebra, Tag 0CQF,
lemma-Rlim-pseudo-coherent-gives-pseudo-coherent
(blueprint: lem-weil-pbc-pseudocoherent-inverse-ring-reconstruction).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory


section ReconstructionHelpers

variable
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (hsurj : ∀ n, Function.Surjective (φ n))
    (hnil : ∀ n, IsNilpotent (RingHom.ker (φ n)))
    (A : Type u) [CommRing A] (q : ∀ n, A →+* R n)
    (hq : ∀ n, q n = (φ n).comp (q (n + 1)))
    (hlim : ∀ x : ∀ n, R n, (∀ n, φ n (x (n + 1)) = x n) →
      ∃! a : A, ∀ n, q n a = x n)
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [∀ n, HasDerivedCategory.{w} (ModuleCat.{max u v} (R n))]
    (L : ∀ n, DerivedCategory (ModuleCat.{max u v} (R (n + 1))) ⥤
      DerivedCategory (ModuleCat.{max u v} (R n)))
    (adjφ : ∀ n, L n ⊣ (ModuleCat.restrictScalars (φ n)).mapDerivedCategory)
    (M : ∀ n, DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} (R n)))
    (adjq : ∀ n, M n ⊣ (ModuleCat.restrictScalars (q n)).mapDerivedCategory)
    (χ : ∀ n, (ModuleCat.restrictScalars (q n)).mapDerivedCategory ≅
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory)
    (hχ : ∀ n (C : CochainComplex (ModuleCat.{max u v} (R n)) ℤ),
      (χ n).hom.app (Q.obj C) ≫
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map
          ((ModuleCat.restrictScalars (φ n)).mapDerivedCategoryFactors.hom.app C) ≫
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj C) =
      (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.hom.app C ≫
        Q.map ((NatIso.mapHomologicalComplex
          (ModuleCat.restrictScalarsComp' (q (n + 1)) (φ n) (q n) (hq n))
          (.up ℤ)).hom.app C))
    (Eₙ : ∀ n, DerivedCategory (ModuleCat.{max u v} (R n)))
    (t : ∀ n, Eₙ (n + 1) ⟶
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.obj (Eₙ n))
    (hred : ∀ n, IsIso (((adjφ n).homEquiv (Eₙ (n + 1)) (Eₙ n)).symm (t n)))
    (hpc : IsPseudoCoherent (Eₙ 0))
    [HasProduct (fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))]
    (E : DerivedCategory (ModuleCat.{max u v} A))
    (pE : E ⟶ ∏ᶜ fun n ↦
      (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))
    (δ : (∏ᶜ fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n)) ⟶
      E⟦(1 : ℤ)⟧)
    (hE : IsDerivedLimitTriangle
      (fun n ↦ (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map (t n) ≫
        (χ n).inv.app (Eₙ n)) E pE δ) 
include R φ hsurj hnil A q hq hlim L adjφ M adjq χ hχ Eₙ t hred hpc E pE δ hE

/-- The compatible finite-free models and all chain-level compatibility clauses.
Source: Stacks Project, More on Algebra, Tag 0CQF.
(blueprint: lem-weil-pbc-pseudocoherent-inverse-ring-reconstruction-models).

Proof plan: inductively apply marked finite-free lifting across each nilpotent quotient, preserving
one common upper cutoff and the transition marking. Lift compatible bases degree by degree, so
all terms become coordinatewise finite free and every transition is coordinate reduction. Form
the termwise inverse-limit complex and use the surjective tower limit theorem to identify its
localized object and projections with the supplied derived limit. Finally apply bounded-flat
K-flatness, derived change of rings, and the normalized coefficient adjunction to establish the
projection and transition comparison equations.
-/
theorem reconstruction_models :
    ∃ (Pₙ : ∀ n, CochainComplex (ModuleCat.{max u v} (R n)) ℤ)
      (b : ℤ) (βₙ : ∀ n, Q.obj (Pₙ n) ≅ Eₙ n)
      (uₙ : ∀ n, Pₙ (n + 1) ⟶
        ((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj (Pₙ n))
      (θₙ : ∀ n, ((ModuleCat.extendScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj
        (Pₙ (n + 1)) ≅ Pₙ n)
      (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (β : Q.obj P ≅ E)
      (p : ∀ n, P ⟶
        ((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).obj (Pₙ n))
      (θ : ∀ n, ((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P ≅ Pₙ n)
      (η : ∀ n, P ⟶ ((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P))
      (γ : ∀ n, (M n).obj (Q.obj P) ≅
        Q.obj (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P)),
      (∀ n, (Pₙ n).IsStrictlyLE b) ∧
      (∀ n i, Module.Free (R n) ((Pₙ n).X i) ∧ Module.Finite (R n) ((Pₙ n).X i)) ∧
      (∀ n i, Function.Surjective ((uₙ n).f i)) ∧
      (∀ n i, ((ModuleCat.extendRestrictScalarsAdj (φ n)).homEquiv
        ((Pₙ (n + 1)).X i) ((Pₙ n).X i) ((θₙ n).hom.f i)) = (uₙ n).f i) ∧
      (∀ n, Q.map (uₙ n) = (βₙ (n + 1)).hom ≫ t n ≫
        (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.map (βₙ n).inv ≫
        (ModuleCat.restrictScalars (φ n)).mapDerivedCategoryFactors.hom.app (Pₙ n)) ∧
      P.IsStrictlyLE b ∧
      (∀ i, Module.Free A (P.X i) ∧ Module.Finite A (P.X i)) ∧
      (∀ n i (y : P.X i), (uₙ n).f i ((p (n + 1)).f i y) = (p n).f i y) ∧
      (∀ i (x : ∀ n, (Pₙ n).X i), (∀ n, (uₙ n).f i (x (n + 1)) = x n) →
        ∃! y : P.X i, ∀ n, (p n).f i y = x n) ∧
      (∀ n, Q.map (p n) ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.inv.app (Pₙ n) ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (βₙ n).hom =
        β.hom ≫ pE ≫ Pi.π _ n) ∧
      (∀ n i, ((ModuleCat.extendRestrictScalarsAdj (q n)).homEquiv
        (P.X i) ((Pₙ n).X i) ((θ n).hom.f i)) = (p n).f i) ∧
      (∀ n i, (η n).f i = (ModuleCat.extendRestrictScalarsAdj (q n)).unit.app (P.X i)) ∧
      (∀ n, (adjq n).unit.app (Q.obj P) ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (γ n).hom ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P) =
        Q.map (η n)) ∧
      (∀ n, (γ n).hom ≫ Q.map (θ n).hom ≫ (βₙ n).hom =
        (M n).map β.hom ≫ ((adjq n).homEquiv E (Eₙ n)).symm (pE ≫ Pi.π _ n)) := by
  sorry

end ReconstructionHelpers

end DerivedCategory
