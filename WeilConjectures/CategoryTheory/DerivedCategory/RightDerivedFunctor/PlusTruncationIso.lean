/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.TruncationTrianglePlus

/-!
# Low degree cohomology of a right derived functor sees only low degrees

Let `F : D⁺(C) ⥤ D⁺(D)` be a triangulated functor which does not lower the cohomological degree,
for instance the right derived functor `R⁺v` of an additive functor `v : C ⥤ D`
(`CategoryTheory.Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE`,
blueprint `lem-weil-pbc-derived-functor-negative-vanishing`). If a morphism `c : L ⟶ M` of
`D⁺(C)` induces isomorphisms on `H^i` for `i ≤ n` and a monomorphism on `H^{n+1}`, then `F c`
induces isomorphisms on `H^j` for `j ≤ n`
(`DerivedCategory.Plus.isIso_homologyFunctor_map_map_of_isIso_homologyFunctor_map`,
`CategoryTheory.Functor.isIso_homologyFunctor_map_rightDerivedFunctorPlus_map`). In particular
`H^n(F(τ_{≤ n} K)) ⟶ H^n(F K)` is an isomorphism
(`CategoryTheory.Functor.isIso_homologyFunctor_map_rightDerivedFunctorPlus_map_truncLEι_app`).

This is blueprint `lem-weil-pbc-derived-functor-truncation-iso` (Stacks, Lemma 05TC (2)).
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- If the first morphism of a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` induces
isomorphisms on `H^i` for `i ≤ n` and a monomorphism on `H^{n+1}`, then `X₃` has no cohomology
in degrees `≤ n`. -/
lemma isZero_homologyFunctor_obj₃_of_isIso_of_mono (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (n : ℤ) (h₁ : ∀ i ≤ n, IsIso ((homologyFunctor C i).map T.mor₁))
    (h₂ : Mono ((homologyFunctor C (n + 1)).map T.mor₁)) (i : ℤ) (hi : i ≤ n) :
    IsZero ((homologyFunctor C i).obj T.obj₃) := by
  have := h₁ i hi
  have hp : (homologyFunctor C i).map T.mor₂ = 0 :=
    (HomologySequence.exact₂ T hT i).epi_f_iff.1 inferInstance
  have : Mono ((homologyFunctor C (i + 1)).map T.mor₁) := by
    by_cases h : i + 1 ≤ n
    · have := h₁ (i + 1) h
      infer_instance
    · obtain rfl : i = n := by lia
      exact h₂
  have hδ : HomologySequence.δ T i (i + 1) rfl = 0 :=
    (HomologySequence.exact₁ T hT i (i + 1)).mono_g_iff.1 this
  exact (HomologySequence.exact₃ T hT i (i + 1)).isZero_of_both_zeros hp hδ

namespace Plus

variable {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]

/-- Let `F : D⁺(C) ⥤ D⁺(D)` be a triangulated functor which does not lower the cohomological
degree. If `c : L ⟶ M` induces isomorphisms on `H^i` for `i ≤ n` and a monomorphism on
`H^{n+1}`, then `F c` induces isomorphisms on `H^j` for `j ≤ n`. -/
lemma isIso_homologyFunctor_map_map_of_isIso_homologyFunctor_map (F : Plus C ⥤ Plus D)
    [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ (X : Plus C) (n : ℤ) [X.IsGE n] (q : ℤ), q < n →
      IsZero ((homologyFunctor D q).obj (F.obj X)))
    {L M : Plus C} (c : L ⟶ M) (n : ℤ)
    (h₁ : ∀ i ≤ n, IsIso ((homologyFunctor C i).map c))
    (h₂ : Mono ((homologyFunctor C (n + 1)).map c)) (j : ℤ) (hj : j ≤ n) :
    IsIso ((homologyFunctor D j).map (F.map c)) := by
  obtain ⟨Z, p, w, hT⟩ := distinguished_cocone_triangle c
  have hZ : Z.IsGE (n + 1) := by
    rw [← isGE_ι_obj_iff, DerivedCategory.isGE_iff]
    intro i hi
    exact isZero_homologyFunctor_obj₃_of_isIso_of_mono _ (ι.map_distinguished _ hT) n h₁ h₂ i
      (by lia)
  exact DerivedCategory.isIso_homologyMap_mor₁ _
    (ι.map_distinguished _ (F.map_distinguished _ hT)) (j - 1) j (by lia)
    (hF Z (n + 1) (j - 1) (by lia)) (hF Z (n + 1) j (by lia))

/-- Let `F : D⁺(C) ⥤ D⁺(D)` be a triangulated functor which does not lower the cohomological
degree. Then the inclusion `τ_{≤ n} K ⟶ K` induces an isomorphism
`H^j(F(τ_{≤ n} K)) ⟶ H^j(F K)` for `j ≤ n`. -/
lemma isIso_homologyFunctor_map_map_truncLEι_app (F : Plus C ⥤ Plus D)
    [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ (X : Plus C) (n : ℤ) [X.IsGE n] (q : ℤ), q < n →
      IsZero ((homologyFunctor D q).obj (F.obj X)))
    (K : Plus C) (n j : ℤ) (hj : j ≤ n) :
    IsIso ((homologyFunctor D j).map (F.map ((truncLEι C n).app K))) :=
  isIso_homologyFunctor_map_map_of_isIso_homologyFunctor_map F hF _ n
    (fun i hi ↦ DerivedCategory.isIso_homologyFunctor_map_truncLEι_app (ι.obj K) n i hi)
    ((DerivedCategory.isZero_homologyFunctor_obj_truncLE (ι.obj K) n (n + 1) (by lia)).mono _)
    j hj

end Plus

end DerivedCategory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C] (F : C ⥤ D) [F.Additive]

open DerivedCategory.Plus in
/-- This is blueprint `lem-weil-pbc-derived-functor-truncation-iso`: if a morphism `c : L ⟶ M`
of `D⁺(C)` induces isomorphisms on `H^i` for `i ≤ n` and a monomorphism on `H^{n+1}`, then
`R⁺F(c)` induces isomorphisms on `H^j` for `j ≤ n`. -/
theorem isIso_homologyFunctor_map_rightDerivedFunctorPlus_map
    {L M : DerivedCategory.Plus C} (c : L ⟶ M) (n : ℤ)
    (h₁ : ∀ i ≤ n, IsIso ((homologyFunctor C i).map c))
    (h₂ : Mono ((homologyFunctor C (n + 1)).map c)) (j : ℤ) (hj : j ≤ n) :
    IsIso ((homologyFunctor D j).map (F.rightDerivedFunctorPlus.map c)) :=
  isIso_homologyFunctor_map_map_of_isIso_homologyFunctor_map F.rightDerivedFunctorPlus
    (fun X n _ q hq ↦ F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE X n hq)
    c n h₁ h₂ j hj

open DerivedCategory.Plus in
/-- This is blueprint `lem-weil-pbc-derived-functor-truncation-iso`, last assertion: the
canonical truncation `τ_{≤ n} K ⟶ K` induces an isomorphism
`H^n(R⁺F(τ_{≤ n} K)) ⟶ H^n(R⁺F(K))` (and similarly in all degrees `j ≤ n`). -/
theorem isIso_homologyFunctor_map_rightDerivedFunctorPlus_map_truncLEι_app
    (K : DerivedCategory.Plus C) (n j : ℤ) (hj : j ≤ n) :
    IsIso ((homologyFunctor D j).map (F.rightDerivedFunctorPlus.map ((truncLEι C n).app K))) :=
  isIso_homologyFunctor_map_map_truncLEι_app F.rightDerivedFunctorPlus
    (fun X n _ q hq ↦ F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE X n hq)
    K n j hj

end CategoryTheory.Functor
