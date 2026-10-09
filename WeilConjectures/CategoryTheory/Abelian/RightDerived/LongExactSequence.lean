/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Resolution

/-!
# The long exact sequence of right derived functors

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has injective
resolutions. A short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` in `C` gives a long exact sequence
```
  ⋯ ⟶ R^q F A ⟶ R^q F B ⟶ R^q F C ⟶ R^{q+1} F A ⟶ R^{q+1} F B ⟶ ⋯
```
(`CategoryTheory.ShortComplex.ShortExact.exists_rightDerived_δ_exact`).

The proof goes through the bounded below derived category: the short exact sequence is a
distinguished triangle `A[0] ⟶ B[0] ⟶ C[0] ⟶ A[0][1]` in `DerivedCategory.Plus C`, the
triangulated functor `R⁺F` sends it to a distinguished triangle, and the homology of a
distinguished triangle is a long exact sequence. Finally `H^q(R⁺F(X[0])) ≅ R^q F X` naturally
in `X` (`Functor.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso`).

## References

* [Stacks Project, Tag 015Q](https://stacks.math.columbia.edu/tag/015Q)
-/

@[expose] public section

namespace CategoryTheory

open Limits Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D]

namespace ShortComplex.ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact)

section Triangle

variable [HasDerivedCategory C]

omit [HasInjectiveResolutions C]

/-- The connecting morphism `C[0] ⟶ A[0][1]` in `DerivedCategory.Plus C` of a short exact
sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`. -/
noncomputable def plusSingleδ :
    (DerivedCategory.Plus.singleFunctor C 0).obj S.X₃ ⟶
      ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧ :=
  DerivedCategory.Plus.ι.preimage (hS.singleδ ≫
    (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
      ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁))

@[reassoc]
lemma ι_map_plusSingleδ :
    DerivedCategory.Plus.ι.map hS.plusSingleδ ≫
        (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁) = hS.singleδ := by
  rw [plusSingleδ, Functor.map_preimage]
  erw [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id (obj := DerivedCategory C) _

/-- The triangle `A[0] ⟶ B[0] ⟶ C[0] ⟶ A[0][1]` in `DerivedCategory.Plus C` of a short exact
sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`. -/
noncomputable def plusSingleTriangle : Triangle (DerivedCategory.Plus C) :=
  Triangle.mk ((DerivedCategory.Plus.singleFunctor C 0).map S.f)
    ((DerivedCategory.Plus.singleFunctor C 0).map S.g) hS.plusSingleδ

lemma plusSingleTriangle_distinguished : hS.plusSingleTriangle ∈ distTriang _ := by
  rw [← DerivedCategory.Plus.ι.map_distinguished_iff]
  refine isomorphic_distinguished _ hS.singleTriangle_distinguished _ ?_
  let i := DerivedCategory.Plus.singleFunctorιIso C 0
  refine Triangle.isoMk _ _ (i.app S.X₁) (i.app S.X₂) (i.app S.X₃) ?_ ?_ ?_
  · exact i.hom.naturality S.f
  · exact i.hom.naturality S.g
  · change (DerivedCategory.Plus.ι.map hS.plusSingleδ ≫
        (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁)) ≫
          (i.hom.app S.X₁)⟦(1 : ℤ)⟧' = i.hom.app S.X₃ ≫ hS.singleδ
    rw [hS.ι_map_plusSingleδ]
    change hS.singleδ ≫ (𝟙 _)⟦(1 : ℤ)⟧' = 𝟙 _ ≫ hS.singleδ
    rw [Functor.map_id, Category.comp_id, Category.id_comp]

variable {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)

lemma plusSingleδ_naturality :
    h₁.plusSingleδ ≫ ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₁)⟦(1 : ℤ)⟧' =
      (DerivedCategory.Plus.singleFunctor C 0).map φ.τ₃ ≫ h₂.plusSingleδ := by
  apply DerivedCategory.Plus.ι.map_injective
  rw [← cancel_mono ((DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app _)]
  simp only [Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality,
    ι_map_plusSingleδ_assoc, ι_map_plusSingleδ]
  exact (ShortComplex.ShortExact.singleTriangle.map h₁ h₂ φ).comm₃

/-- The morphism of triangles `plusSingleTriangle h₁ ⟶ plusSingleTriangle h₂` induced by a
morphism of short exact sequences. -/
noncomputable def plusSingleTriangleMap : h₁.plusSingleTriangle ⟶ h₂.plusSingleTriangle where
  hom₁ := (DerivedCategory.Plus.singleFunctor C 0).map φ.τ₁
  hom₂ := (DerivedCategory.Plus.singleFunctor C 0).map φ.τ₂
  hom₃ := (DerivedCategory.Plus.singleFunctor C 0).map φ.τ₃
  comm₁ := by
    let s := DerivedCategory.Plus.singleFunctor C 0
    exact ((s.map_comp _ _).symm.trans (congrArg s.map φ.comm₁₂.symm)).trans (s.map_comp _ _)
  comm₂ := by
    let s := DerivedCategory.Plus.singleFunctor C 0
    exact ((s.map_comp _ _).symm.trans (congrArg s.map φ.comm₂₃.symm)).trans (s.map_comp _ _)
  comm₃ := plusSingleδ_naturality h₁ h₂ φ

end Triangle

variable (F : C ⥤ D) [F.Additive]

/-- The connecting morphism `δ : R^q F C ⟶ R^{q+1} F A` of the long exact sequence of right
derived functors of a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`: the connecting morphism of the
long exact homology sequence of the distinguished triangle `R⁺F(A[0]) ⟶ R⁺F(B[0]) ⟶ R⁺F(C[0]) ⟶`
in the bounded below derived category of `D`. -/
noncomputable def rightDerivedδ (q : ℕ) :
    (F.rightDerived q).obj S.X₃ ⟶ (F.rightDerived (q + 1)).obj S.X₁ :=
  letI := HasDerivedCategory.standard C
  letI := HasDerivedCategory.standard D
  haveI := enoughInjectives_of_hasInjectiveResolutions (C := C)
  (F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q).inv.app S.X₃ ≫
    DerivedCategory.HomologySequence.δ
      ((F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
        hS.plusSingleTriangle) q ((q + 1 : ℕ) : ℤ) (by push_cast; rfl) ≫
    (F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso (q + 1)).hom.app S.X₁

/-- The connecting morphisms of the long exact sequence of right derived functors are natural
in the short exact sequence. -/
@[reassoc]
lemma rightDerivedδ_naturality {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (q : ℕ) :
    (F.rightDerived q).map φ.τ₃ ≫ h₂.rightDerivedδ F q =
      h₁.rightDerivedδ F q ≫ (F.rightDerived (q + 1)).map φ.τ₁ := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  have := enoughInjectives_of_hasInjectiveResolutions (C := C)
  let e (n : ℕ) := F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n
  let ψ := (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.map
    (plusSingleTriangleMap h₁ h₂ φ)
  have hψ := (DerivedCategory.homologyFunctor D 0).homologySequenceδ_naturality _ _ ψ q
    ((q + 1 : ℕ) : ℤ) (by push_cast; rfl)
  have h₃ := (e q).inv.naturality φ.τ₃
  have h₁' := (e (q + 1)).hom.naturality φ.τ₁
  dsimp [rightDerivedδ] at hψ h₃ ⊢
  rw [reassoc_of% h₃]
  erw [reassoc_of% hψ]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg ((e q).inv.app S₁.X₃ ≫ ·) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  erw [h₁']
  rfl


section Exact

variable (q : ℕ)

include hS

private lemma rightDerivedδ_aux :
    letI := HasDerivedCategory.standard C
    letI := HasDerivedCategory.standard D
    haveI := enoughInjectives_of_hasInjectiveResolutions (C := C)
    ((F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
      hS.plusSingleTriangle) ∈ distTriang _ := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  have := enoughInjectives_of_hasInjectiveResolutions (C := C)
  exact Functor.map_distinguished _ _ hS.plusSingleTriangle_distinguished

@[reassoc (attr := simp)]
lemma rightDerived_map_g_comp_δ :
    (F.rightDerived q).map S.g ≫ hS.rightDerivedδ F q = 0 := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  have := enoughInjectives_of_hasInjectiveResolutions (C := C)
  let e (n : ℕ) := F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n
  refine ((e q).inv.naturality_assoc S.g _).trans ?_
  refine (congrArg ((e q).inv.app S.X₂ ≫ ·)
    (DerivedCategory.HomologySequence.comp_δ_assoc _ (hS.rightDerivedδ_aux F) q _
      (by push_cast; rfl) _)).trans ?_
  erw [zero_comp, comp_zero]

@[reassoc (attr := simp)]
lemma rightDerivedδ_comp_map_f :
    hS.rightDerivedδ F q ≫ (F.rightDerived (q + 1)).map S.f = 0 := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  have := enoughInjectives_of_hasInjectiveResolutions (C := C)
  let e (n : ℕ) := F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n
  let T' := (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
    hS.plusSingleTriangle
  let δ' := DerivedCategory.HomologySequence.δ T' q ((q + 1 : ℕ) : ℤ) (by push_cast; rfl)
  change ((e q).inv.app S.X₃ ≫ δ' ≫ (e (q + 1)).hom.app S.X₁) ≫ _ = 0
  rw [Category.assoc]
  refine (congrArg ((e q).inv.app S.X₃ ≫ ·) (Category.assoc δ' _ _)).trans ?_
  refine (congrArg (fun x ↦ (e q).inv.app S.X₃ ≫ δ' ≫ x)
    ((e (q + 1)).hom.naturality S.f).symm).trans ?_
  refine (congrArg ((e q).inv.app S.X₃ ≫ ·)
    (DerivedCategory.HomologySequence.δ_comp_assoc T' (hS.rightDerivedδ_aux F) q _
      (by push_cast; rfl) _)).trans ?_
  erw [zero_comp, comp_zero]

/-- Exactness of `R^q F B ⟶ R^q F C ⟶ R^{q+1} F A`. -/
lemma rightDerived_exact₂ :
    (ShortComplex.mk _ _ (hS.rightDerived_map_g_comp_δ F q)).Exact := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  have := enoughInjectives_of_hasInjectiveResolutions (C := C)
  let e (n : ℕ) := F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (DerivedCategory.HomologySequence.exact₃ _ (hS.rightDerivedδ_aux F) q _ (by push_cast; rfl))
  exact ShortComplex.isoMk ((e q).app S.X₂) ((e q).app S.X₃) ((e (q + 1)).app S.X₁)
    ((e q).hom.naturality S.g).symm (Iso.hom_inv_id_app_assoc (e q) S.X₃ _)

/-- Exactness of `R^q F C ⟶ R^{q+1} F A ⟶ R^{q+1} F B`. -/
lemma rightDerived_exact₃ :
    (ShortComplex.mk _ _ (hS.rightDerivedδ_comp_map_f F q)).Exact := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  have := enoughInjectives_of_hasInjectiveResolutions (C := C)
  let e (n : ℕ) := F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (DerivedCategory.HomologySequence.exact₁ _ (hS.rightDerivedδ_aux F) q _ (by push_cast; rfl))
  exact ShortComplex.isoMk ((e q).app S.X₃) ((e (q + 1)).app S.X₁) ((e (q + 1)).app S.X₂)
    (Iso.hom_inv_id_app_assoc (e q) S.X₃ _) ((e (q + 1)).hom.naturality S.f).symm

/-- Exactness of `R^q F A ⟶ R^q F B ⟶ R^q F C`. -/
lemma rightDerived_exact₁ :
    (ShortComplex.mk ((F.rightDerived q).map S.f) ((F.rightDerived q).map S.g)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero])).Exact := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  have := enoughInjectives_of_hasInjectiveResolutions (C := C)
  let e (n : ℕ) := F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (DerivedCategory.HomologySequence.exact₂ _ (hS.rightDerivedδ_aux F) q)
  exact ShortComplex.isoMk ((e q).app S.X₁) ((e q).app S.X₂) ((e q).app S.X₃)
    ((e q).hom.naturality S.f).symm ((e q).hom.naturality S.g).symm

end Exact

include hS in
/-- The long exact sequence of the right derived functors of `F`: a short exact sequence
`0 ⟶ A ⟶ B ⟶ C ⟶ 0` gives a connecting morphism `δ : R^q F C ⟶ R^{q+1} F A` such that
```
  R^q F B ──R^q F g──▶ R^q F C ──δ──▶ R^{q+1} F A ──R^{q+1} F f──▶ R^{q+1} F B
```
is exact at `R^q F C` and at `R^{q+1} F A`. The connecting morphism is the one of the long
exact homology sequence of the distinguished triangle `R⁺F(A[0]) ⟶ R⁺F(B[0]) ⟶ R⁺F(C[0]) ⟶`
in the bounded below derived category of `D`. (blueprint: `lemma-weil-pbc-leray-acyclicity`,
Step 0) -/
theorem exists_rightDerived_δ_exact (q : ℕ) :
    ∃ (δ : (F.rightDerived q).obj S.X₃ ⟶ (F.rightDerived (q + 1)).obj S.X₁)
      (w₁ : (F.rightDerived q).map S.g ≫ δ = 0) (w₂ : δ ≫ (F.rightDerived (q + 1)).map S.f = 0),
      (ShortComplex.mk _ _ w₁).Exact ∧ (ShortComplex.mk _ _ w₂).Exact :=
  ⟨hS.rightDerivedδ F q, hS.rightDerived_map_g_comp_δ F q, hS.rightDerivedδ_comp_map_f F q,
    hS.rightDerived_exact₂ F q, hS.rightDerived_exact₃ F q⟩

end ShortComplex.ShortExact

end CategoryTheory
