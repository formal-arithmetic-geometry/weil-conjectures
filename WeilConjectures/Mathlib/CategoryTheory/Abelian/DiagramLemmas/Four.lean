/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-!
# The four lemma with arbitrary zero morphisms

Forms of the four lemma (`CategoryTheory.ShortComplex.mono_of_epi_of_epi_of_mono`) in which the
objects and maps are named explicitly and the zero morphisms of the abelian category are an
arbitrary instance. They apply as they stand to categories of sheaves, whose zero morphisms come
from the full subcategory of sheaves rather than from the abelian structure: comparing the two
instances, and identifying the maps of a short complex with its projections, is expensive for
the kernel.

## Main statements

- `CategoryTheory.Abelian.mono_of_epi_of_epi_of_mono_of_comm`: the four lemma for a morphism
  of short complexes given by three maps and two commutative squares.
- `CategoryTheory.Abelian.mono_cokernelDesc_of_comm`: the induced map out of the cokernel of
  `b` is a monomorphism when `b` is related by an epimorphism and an isomorphism to the first
  map of an exact sequence.
-/

@[expose] public section

namespace CategoryTheory.Abelian

open Limits

variable {D : Type*} [Category* D] [Abelian D] [Z : HasZeroMorphisms D]

include Z in
/-- The four lemma: in a commutative diagram
```
A₁ --f--> A₂ --g--> A₃
|α₁       |α₂       |α₃
v         v         v
B₁ --f'-> B₂ --g'-> B₃
```
with `g` an epimorphism and exact bottom row, if `α₁` is an epimorphism and `α₂` a
monomorphism then `α₃` is a monomorphism. -/
theorem mono_of_epi_of_epi_of_mono_of_comm {A₁ A₂ A₃ B₁ B₂ B₃ : D} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃)
    (f' : B₁ ⟶ B₂) (g' : B₂ ⟶ B₃) (α₁ : A₁ ⟶ B₁) (α₂ : A₂ ⟶ B₂) (α₃ : A₃ ⟶ B₃)
    (w₁ : α₁ ≫ f' = f ≫ α₂) (w₂ : α₂ ≫ g' = g ≫ α₃) (wS : f ≫ g = 0) (wT : f' ≫ g' = 0)
    (hT : (ShortComplex.mk f' g' wT).Exact) [Epi g] [Epi α₁] [Mono α₂] : Mono α₃ := by
  obtain rfl : Z = Preadditive.preadditiveHasZeroMorphisms := Subsingleton.elim _ _
  exact ShortComplex.mono_of_epi_of_epi_of_mono
    (R₁ := ShortComplex.mk f g wS) (R₂ := ShortComplex.mk f' g' wT)
    { τ₁ := α₁, τ₂ := α₂, τ₃ := α₃, comm₁₂ := w₁, comm₂₃ := w₂ } hT ‹_› ‹_› ‹_›

include Z in
/-- Let `δT : Y ⟶ B`, `t : B ⟶ C` be exact, and let `b : A ⟶ B` with `b ≫ t = 0` satisfy
`δS ≫ b = c ≫ δT` for an epimorphism `δS : X ⟶ A` and an isomorphism `c : X ⟶ Y`. Then the map
`cokernel b ⟶ C` induced by `t` is a monomorphism. -/
theorem mono_cokernelDesc_of_comm {X Y A B C : D} (δS : X ⟶ A) (c : X ⟶ Y) (δT : Y ⟶ B)
    (b : A ⟶ B) (t : B ⟶ C) (hδ : δS ≫ b = c ≫ δT) (wT : δT ≫ t = 0)
    (hT : (ShortComplex.mk δT t wT).Exact) (hbt : b ≫ t = 0) [Epi δS] [IsIso c]
    [HasCokernel b] : Mono (cokernel.desc b t hbt) := by
  obtain rfl : Z = Preadditive.preadditiveHasZeroMorphisms := Subsingleton.elim _ _
  have hct : (c ≫ δT) ≫ t = 0 := by rw [Category.assoc, wT, comp_zero]
  have h₁ : (ShortComplex.mk (c ≫ δT) t hct).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      ({ τ₁ := c, τ₂ := 𝟙 _, τ₃ := 𝟙 _ } : ShortComplex.mk (c ≫ δT) t hct ⟶
        ShortComplex.mk δT t wT)).2 hT
  have h₂ : (ShortComplex.mk b t hbt).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      ({ τ₁ := δS, τ₂ := 𝟙 _, τ₃ := 𝟙 _, comm₁₂ := by simp [hδ] } :
        ShortComplex.mk (c ≫ δT) t hct ⟶ ShortComplex.mk b t hbt)).1 h₁
  exact h₂.mono_cokernelDesc

end CategoryTheory.Abelian
