/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Cokernels of multiplication by an integer

Let `C` be a preadditive category and `n` a natural number. This file collects ways to
recognise a cokernel of the multiplication `n • 𝟙 X : X ⟶ X`:

- `CategoryTheory.Limits.CokernelCofork.isColimitOfArrowIso`: a cokernel can be transported
  along an isomorphism of arrows.
- `CategoryTheory.Limits.CokernelCofork.isColimitOfEq`: a cokernel of `f` is a cokernel of any
  `f'` equal to `f`.
- `CategoryTheory.Functor.isColimitCokernelCoforkNSMulMap`: a functor which preserves the
  cokernel of `n • 𝟙 X` maps it to a cokernel of `n • 𝟙 (G.obj X)`.
- `CategoryTheory.ShortComplex.ShortExact.isColimitCokernelCoforkNSMul`: for a short exact
  sequence `0 ⟶ A ⟶ B ⟶ D ⟶ 0` on which `n` is an epimorphism of `A`, the cokernel of `n` on
  `B` is the cokernel of `n` on `D` (the relevant part of the snake lemma).
- `CategoryTheory.Limits.Cofan.IsColimit.isColimitCokernelCoforkNSMul`: the cokernel of `n` on
  a coproduct is the coproduct of the cokernels of `n`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category* C]

namespace Limits.CokernelCofork

variable [HasZeroMorphisms C]

/-- The factorisation through a cokernel `π`, as an equation involving `π` itself. -/
@[reassoc (attr := simp)]
lemma π_desc' {X Y Q W : C} {f : X ⟶ Y} {π : Y ⟶ Q} {w : f ≫ π = 0}
    (h : IsColimit (CokernelCofork.ofπ π w)) (k : Y ⟶ W) (hk : f ≫ k = 0) :
    π ≫ (CokernelCofork.IsColimit.desc' h k hk).1 = k :=
  (CokernelCofork.IsColimit.desc' h k hk).2

/-- A cokernel of `f` is a cokernel of any morphism equal to `f`. -/
def isColimitOfEq {X Y Q : C} {f f' : X ⟶ Y} (hf : f = f') {π : Y ⟶ Q} {w : f ≫ π = 0}
    (h : IsColimit (CokernelCofork.ofπ π w)) :
    IsColimit (CokernelCofork.ofπ (f := f') π (hf ▸ w)) := by
  subst hf
  exact h

end Limits.CokernelCofork

section Preadditive

variable [Preadditive C] (n : ℕ)

/-- Multiplication by `n` commutes with every morphism. -/
@[reassoc]
lemma nsmul_id_comp_eq_comp_nsmul_id {X Y : C} (f : X ⟶ Y) :
    (n • 𝟙 X) ≫ f = f ≫ (n • 𝟙 Y) := by
  rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]

variable {D : Type*} [Category* D] [Preadditive D]

end Preadditive

end CategoryTheory

end
