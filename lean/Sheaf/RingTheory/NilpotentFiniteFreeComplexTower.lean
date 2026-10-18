/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.RingTheory.NilpotentMarkedFreeComplexStep

/-! # Compatible finite-free complex towers

Source: Stacks Project, More on Algebra, Tag 0CQF.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Compatible marked finite-free models with a single upper cutoff.
Source: Stacks Project, Tag 0CQF, first induction in the proof
(blueprint: lem-weil-pbc-nilpotent-finite-free-complex-tower).

Proof: Inductively apply nilpotent invariance to the given derived reduction to obtain
pseudo-coherence at every level. Choose a bounded-above finite-free model at level zero.
At the next level identify the surjective ring map with its kernel quotient. Nilpotence
makes every one-plus-kernel element a unit, by a finite geometric series. Apply marked
free-complex lifting to the previous model, the prescribed reduction isomorphism and the
same cutoff. Transport along the quotient-ring isomorphism. Define the transition as the
ordinary scalar-extension unit followed by the lifted marking. This transition is
surjective, because every pure tensor is a scalar multiple of a unit tensor and the ring
map is surjective. The normalized derived adjunction identifies its localization with
the specified transition. Dependent choice iterates the construction. Rank-zero terms
and zero rings are included in nilpotent lifting. -/
theorem exists_nilpotent_finiteFree_complexTower
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (hsurj : ∀ n, Function.Surjective (φ n))
    (hnil : ∀ n, IsNilpotent (RingHom.ker (φ n)))
    [∀ n, HasDerivedCategory.{w} (ModuleCat.{max u v} (R n))]
    (L : ∀ n, DerivedCategory (ModuleCat.{max u v} (R (n + 1))) ⥤
      DerivedCategory (ModuleCat.{max u v} (R n)))
    (adjφ : ∀ n, L n ⊣ (ModuleCat.restrictScalars (φ n)).mapDerivedCategory)
    (Eₙ : ∀ n, DerivedCategory (ModuleCat.{max u v} (R n)))
    (t : ∀ n, Eₙ (n + 1) ⟶
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.obj (Eₙ n))
    (hred : ∀ n, IsIso (((adjφ n).homEquiv (Eₙ (n + 1)) (Eₙ n)).symm (t n)))
    (hpc : IsPseudoCoherent (Eₙ 0))
 :
    ∃ (Pₙ : ∀ n, CochainComplex (ModuleCat.{max u v} (R n)) ℤ)
      (b : ℤ) (βₙ : ∀ n, Q.obj (Pₙ n) ≅ Eₙ n)
      (uₙ : ∀ n, Pₙ (n + 1) ⟶
        ((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj (Pₙ n))
      (θₙ : ∀ n, ((ModuleCat.extendScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj
        (Pₙ (n + 1)) ≅ Pₙ n),
      (∀ n, (Pₙ n).IsStrictlyLE b) ∧
      (∀ n i, Module.Free (R n) ((Pₙ n).X i) ∧ Module.Finite (R n) ((Pₙ n).X i)) ∧
      (∀ n i, Function.Surjective ((uₙ n).f i)) ∧
      (∀ n i, ((ModuleCat.extendRestrictScalarsAdj (φ n)).homEquiv
        ((Pₙ (n + 1)).X i) ((Pₙ n).X i) ((θₙ n).hom.f i)) = (uₙ n).f i) ∧
      (∀ n, Q.map (uₙ n) = (βₙ (n + 1)).hom ≫ t n ≫
        (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.map (βₙ n).inv ≫
        (ModuleCat.restrictScalars (φ n)).mapDerivedCategoryFactors.hom.app (Pₙ n)) := by
  classical
  obtain ⟨P₀, b, hP₀, hterms₀, ⟨β₀⟩⟩ := hpc
  let Model := fun n ↦ Σ P : CochainComplex (ModuleCat.{max u v} (R n)) ℤ,
    { β : Q.obj P ≅ Eₙ n // P.IsStrictlyLE b ∧
      (∀ i, Module.Free (R n) (P.X i) ∧ Module.Finite (R n) (P.X i)) }
  have step (n : ℕ) (P : Model n) : ∃ (P' : Model (n + 1))
      (u : P'.1 ⟶
        ((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj P.1)
      (θ : ((ModuleCat.extendScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj P'.1 ≅ P.1),
      (∀ i, Function.Surjective (u.f i)) ∧
      (∀ i, (ModuleCat.extendRestrictScalarsAdj (φ n)).homEquiv
        (P'.1.X i) (P.1.X i) (θ.hom.f i) = u.f i) ∧
      Q.map u = P'.2.val.hom ≫ t n ≫
        (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.map P.2.val.inv ≫
        (ModuleCat.restrictScalars (φ n)).mapDerivedCategoryFactors.hom.app P.1 := by
    obtain ⟨P', β', u, θ, hb, ht, hs, hθ, hu⟩ :=
      exists_nilpotent_marked_finiteFree_step (φ n) (hsurj n) (hnil n)
        (L n) (adjφ n) (Eₙ (n + 1)) (Eₙ n) (t n) (hred n)
        P.1 b P.2.property.1 P.2.property.2 P.2.val
    exact ⟨⟨P', β', hb, ht⟩, u, θ, hs, hθ, hu⟩
  let models : ∀ n, Model n := Nat.rec ⟨P₀, β₀, hP₀, hterms₀⟩
    (fun n P ↦ (step n P).choose)
  have hmodels (n : ℕ) : ∃
      (u : (models (n + 1)).1 ⟶
        ((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj (models n).1)
      (θ : ((ModuleCat.extendScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj
        (models (n + 1)).1 ≅ (models n).1),
      (∀ i, Function.Surjective (u.f i)) ∧
      (∀ i, (ModuleCat.extendRestrictScalarsAdj (φ n)).homEquiv
        ((models (n + 1)).1.X i) ((models n).1.X i) (θ.hom.f i) = u.f i) ∧
      Q.map u = (models (n + 1)).2.val.hom ≫ t n ≫
        (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.map (models n).2.val.inv ≫
        (ModuleCat.restrictScalars (φ n)).mapDerivedCategoryFactors.hom.app (models n).1 :=
    (step n (models n)).choose_spec
  choose u θ hs hθ hu using hmodels
  exact ⟨fun n ↦ (models n).1, b, fun n ↦ (models n).2.val, u, θ,
    fun n ↦ (models n).2.property.1, fun n ↦ (models n).2.property.2, hs, hθ, hu⟩

end DerivedCategory
