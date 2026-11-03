/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Five-term Hom exactness using a shift of the source

Source: Stacks 05QK and 0147, exactness of Hom on distinguished triangles.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace CategoryTheory.Pretriangulated

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A]
  [HasShift A ℤ] [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]

/-- The additive bijection on Hom induced by the shift equivalence.
Source: Stacks 0145 (blueprint: lem-sf-triangle-source-shift-hom-exact). -/
def shiftOneHomEquiv (M N : A) : (M ⟶ N) ≃+ (M⟦(1 : ℤ)⟧ ⟶ N⟦(1 : ℤ)⟧) where
  toEquiv := (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor A (1 : ℤ))).homEquiv
  map_add' _ _ := (shiftFunctor A (1 : ℤ)).map_add

/-- Postcomposition is an additive map on Hom.
Source: Stacks 0147 (blueprint: lem-sf-triangle-source-shift-hom-exact). -/
def postcomposeHom (M : A) {P Q : A} (b : P ⟶ Q) : (M ⟶ P) →+ (M ⟶ Q) where
  toFun x := x ≫ b
  map_zero' := zero_comp
  map_add' _ _ := by simp only [Preadditive.add_comp]

/-- The connecting Hom map is the unique inverse shift of composition with the boundary.
Source: Stacks 0147 (blueprint: lem-sf-triangle-source-shift-hom-exact). -/
def sourceShiftConnecting (M : A) {N Q : A} (c : Q ⟶ N⟦(1 : ℤ)⟧) :
    (M⟦(1 : ℤ)⟧ ⟶ Q) →+ (M ⟶ N) :=
  (shiftOneHomEquiv M N).symm.toAddMonoidHom.comp (postcomposeHom _ c)

@[simp]
theorem sourceShiftConnecting_shift (M : A) {N Q : A}
    (c : Q ⟶ N⟦(1 : ℤ)⟧) (x : M⟦(1 : ℤ)⟧ ⟶ Q) :
    (sourceShiftConnecting M c x)⟦(1 : ℤ)⟧' = x ≫ c :=
  (shiftOneHomEquiv M N).apply_symm_apply _

/-- Hom on a distinguished triangle is exact in the three consecutive places needed
for the vertex-edge sequence, writing the preceding terms with a shifted source.
Source: Stacks 0147 and 05QK
(blueprint: lem-sf-triangle-source-shift-hom-exact).
Proof: exactness at the third vertex and at the second vertex is the corresponding
coyoneda exactness theorem. For the central term, shift a map and use exactness at
the shifted first vertex; the shift equivalence reflects both equality and zero. -/
theorem sourceShiftHom_exact (T : Triangle A) (hT : T ∈ distTriang A) (M : A) :
    Function.Exact (postcomposeHom (M⟦(1 : ℤ)⟧) T.mor₂)
      (sourceShiftConnecting M T.mor₃) ∧
    Function.Exact (sourceShiftConnecting M T.mor₃) (postcomposeHom M T.mor₁) ∧
    Function.Exact (postcomposeHom M T.mor₁) (postcomposeHom M T.mor₂) := by
  have hz₁ := comp_distTriang_mor_zero₁₂ T hT
  have hz₂ := comp_distTriang_mor_zero₂₃ T hT
  have hz₃ := comp_distTriang_mor_zero₃₁ T hT
  refine ⟨?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have hx' : x ≫ T.mor₃ = 0 := by
        rw [← sourceShiftConnecting_shift, hx, Functor.map_zero]
      obtain ⟨y, hy⟩ := T.coyoneda_exact₃ hT x hx'
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, rfl⟩
      apply (shiftOneHomEquiv M T.obj₁).injective
      change (sourceShiftConnecting M T.mor₃ (y ≫ T.mor₂))⟦(1 : ℤ)⟧' =
        (0 : M ⟶ T.obj₁)⟦(1 : ℤ)⟧'
      rw [sourceShiftConnecting_shift, Category.assoc, hz₂, comp_zero, Functor.map_zero]
  · intro f
    constructor
    · intro hf
      have hf' : f⟦(1 : ℤ)⟧' ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 := by
        change f ≫ T.mor₁ = 0 at hf
        rw [← Functor.map_comp, hf, Functor.map_zero]
      obtain ⟨x, hx⟩ := T.coyoneda_exact₁ hT (f⟦(1 : ℤ)⟧') hf'
      refine ⟨x, ?_⟩
      apply (shiftOneHomEquiv M T.obj₁).injective
      exact (sourceShiftConnecting_shift M T.mor₃ x).trans hx.symm
    · rintro ⟨x, rfl⟩
      change sourceShiftConnecting M T.mor₃ x ≫ T.mor₁ = 0
      apply (shiftFunctor A (1 : ℤ)).map_injective
      rw [Functor.map_comp, sourceShiftConnecting_shift, Category.assoc, hz₃,
        comp_zero, Functor.map_zero]
  · intro f
    constructor
    · intro hf
      obtain ⟨g, hg⟩ := T.coyoneda_exact₂ hT f hf
      exact ⟨g, hg.symm⟩
    · rintro ⟨g, rfl⟩
      change (g ≫ T.mor₁) ≫ T.mor₂ = 0
      rw [Category.assoc, hz₁, comp_zero]

/-- Connecting Hom maps commute with a morphism of triangle boundaries and source maps.
Source: Stacks 0147
(blueprint: lem-sf-triangle-source-shift-hom-exact).
Proof: apply the faithful shift functor; the desired identity becomes the boundary
naturality square, with associativity of composition. -/
theorem sourceShiftConnecting_natural {M M' N N' Q Q' : A}
    (c : Q ⟶ N⟦(1 : ℤ)⟧) (c' : Q' ⟶ N'⟦(1 : ℤ)⟧)
    (f : M' ⟶ M) (g : N ⟶ N') (q : Q ⟶ Q')
    (h : c ≫ g⟦(1 : ℤ)⟧' = q ≫ c') (x : M⟦(1 : ℤ)⟧ ⟶ Q) :
    sourceShiftConnecting M' c' (f⟦(1 : ℤ)⟧' ≫ x ≫ q) =
      f ≫ sourceShiftConnecting M c x ≫ g := by
  apply (shiftFunctor A (1 : ℤ)).map_injective
  simp only [sourceShiftConnecting_shift, Functor.map_comp, Category.assoc, ← h]

end CategoryTheory.Pretriangulated
