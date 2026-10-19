/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# Mates along an isomorphism of left adjoints

Source: the Weil conjectures blueprint, `sec-trace-formula`, `sk-d-weil`,
lemma `lem-trf-adjoint-mate` (blueprint: lem-trf-adjoint-mate).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- An isomorphism of exact left adjoints canonically identifies their right adjoints,
with the displayed mate formulas, both unit and counit identities, and uniqueness among
isomorphisms satisfying the forward unit and counit identities.
Source: Weil conjectures blueprint, `sec-trace-formula`, `sk-d-weil`,
lemma `lem-trf-adjoint-mate` (blueprint: lem-trf-adjoint-mate).

Proof: Apply `conjugateIsoEquiv adj₁ adj₂ α.symm`, supplied by
[def-weil-pbc-adjunction-conjugate]. Its hom is the conjugate of `α.inv`, and its inverse
is the conjugate of `α.hom` under the reversed adjunctions; expansion gives the two
component formulas. For the forward unit identity, expand the mate, move the units
using naturality of `adj₂.unit` and `α.inv`, cancel by the triangle identity for `adj₁`,
and compose with `G₂.map (α.hom.app c)`. Interchanging the adjunctions and replacing
`α` by `α.symm` gives the inverse unit identity. For the forward counit identity,
expand the mate, use naturality of `α.inv` and the triangle identity for `adj₂`, then
naturality of `α` to obtain the stated pasting with `F₁.map (β.hom.app d)`.
Interchange the adjunctions for the reversed counit identity. Finally the unit identities
for any competing `β'` and for `β` imply equality after precomposition with `adj₁.unit`
and cancellation of the image of `α`. Naturality of `β'` at `adj₁.counit.app d` and the
triangle identity express `β'.hom.app d` as
`adj₁.unit.app (G₁.obj d) ≫ β'.hom.app (F₁.obj (G₁.obj d)) ≫ G₂.map (adj₁.counit.app d)`.
The same expression holds for `β`, so the unit equality at `G₁.obj d` gives equality of
all components. Extensionality of natural transformations and isomorphisms finishes. -/
theorem adjointMate
    {C₁ : Type u₁} {C₂ : Type u₂} [Category.{v₁} C₁] [Category.{v₂} C₂]
    [Preadditive C₁] [Preadditive C₂] [HasZeroObject C₁] [HasZeroObject C₂]
    [HasShift C₁ ℤ] [HasShift C₂ ℤ]
    [∀ n : ℤ, (shiftFunctor C₁ n).Additive] [∀ n : ℤ, (shiftFunctor C₂ n).Additive]
    [Pretriangulated C₁] [Pretriangulated C₂] [IsTriangulated C₁] [IsTriangulated C₂]
    (F₁ F₂ : C₁ ⥤ C₂) (G₁ G₂ : C₂ ⥤ C₁)
    [F₁.CommShift ℤ] [F₂.CommShift ℤ] [G₁.CommShift ℤ] [G₂.CommShift ℤ]
    [F₁.IsTriangulated] [F₂.IsTriangulated] [G₁.IsTriangulated] [G₂.IsTriangulated]
    (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂) (α : F₁ ≅ F₂) :
    ∃ β : G₁ ≅ G₂,
      (∀ d : C₂, β.hom.app d =
        adj₂.unit.app (G₁.obj d) ≫ G₂.map (α.inv.app (G₁.obj d)) ≫
          G₂.map (adj₁.counit.app d)) ∧
      (∀ d : C₂, β.inv.app d =
        adj₁.unit.app (G₂.obj d) ≫ G₁.map (α.hom.app (G₂.obj d)) ≫
          G₁.map (adj₂.counit.app d)) ∧
      (∀ c : C₁, adj₁.unit.app c ≫ β.hom.app (F₁.obj c) ≫ G₂.map (α.hom.app c) =
        adj₂.unit.app c) ∧
      (∀ d : C₂, F₁.map (β.hom.app d) ≫ α.hom.app (G₂.obj d) ≫ adj₂.counit.app d =
        adj₁.counit.app d) ∧
      (∀ c : C₁, adj₂.unit.app c ≫ β.inv.app (F₂.obj c) ≫ G₁.map (α.inv.app c) =
        adj₁.unit.app c) ∧
      (∀ d : C₂, F₂.map (β.inv.app d) ≫ α.inv.app (G₁.obj d) ≫ adj₁.counit.app d =
        adj₂.counit.app d) ∧
      (∀ β' : G₁ ≅ G₂,
        (∀ c : C₁, adj₁.unit.app c ≫ β'.hom.app (F₁.obj c) ≫ G₂.map (α.hom.app c) =
          adj₂.unit.app c) →
        (∀ d : C₂, F₁.map (β'.hom.app d) ≫ α.hom.app (G₂.obj d) ≫
          adj₂.counit.app d = adj₁.counit.app d) →
        β' = β) := by
  let β := conjugateIsoEquiv adj₁ adj₂ α.symm
  have hunit (c : C₁) :
      adj₁.unit.app c ≫ β.hom.app (F₁.obj c) ≫ G₂.map (α.hom.app c) =
        adj₂.unit.app c := by
    change adj₁.unit.app c ≫ (conjugateEquiv adj₁ adj₂ α.inv).app _ ≫ _ = _
    rw [← Category.assoc, unit_conjugateEquiv]
    simp [Category.assoc, ← G₂.map_comp]
  refine ⟨β, ?_, ?_, hunit, ?_, ?_, ?_, ?_⟩
  · intro d
    simp [β, conjugateEquiv_apply_app]
  · intro d
    simp [β, conjugateEquiv_apply_app]
  · intro d
    change F₁.map ((conjugateEquiv adj₁ adj₂ α.inv).app d) ≫ _ ≫ _ = _
    rw [α.hom.naturality_assoc, conjugateEquiv_counit]
    simp
  · intro c
    change adj₂.unit.app c ≫ (conjugateEquiv adj₂ adj₁ α.hom).app _ ≫ _ = _
    rw [← Category.assoc, unit_conjugateEquiv]
    simp [Category.assoc, ← G₁.map_comp]
  · intro d
    change F₂.map ((conjugateEquiv adj₂ adj₁ α.hom).app d) ≫ _ ≫ _ = _
    rw [α.inv.naturality_assoc, conjugateEquiv_counit]
    simp
  · intro β' hunit' _
    have h (c : C₁) : adj₁.unit.app c ≫ β'.hom.app (F₁.obj c) =
        adj₁.unit.app c ≫ β.hom.app (F₁.obj c) := by
      apply (cancel_mono (G₂.map (α.hom.app c))).mp
      simpa only [Category.assoc] using (hunit' c).trans (hunit c).symm
    apply Iso.ext
    ext d
    calc
      β'.hom.app d = adj₁.unit.app (G₁.obj d) ≫
          β'.hom.app (F₁.obj (G₁.obj d)) ≫ G₂.map (adj₁.counit.app d) := by
        rw [← β'.hom.naturality, ← Category.assoc]
        simp
      _ = adj₁.unit.app (G₁.obj d) ≫
          β.hom.app (F₁.obj (G₁.obj d)) ≫ G₂.map (adj₁.counit.app d) := by
        rw [← Category.assoc, h, Category.assoc]
      _ = β.hom.app d := by
        rw [← β.hom.naturality, ← Category.assoc]
        simp

end CategoryTheory
