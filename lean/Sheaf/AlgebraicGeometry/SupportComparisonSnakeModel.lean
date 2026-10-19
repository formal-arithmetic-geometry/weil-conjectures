/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Transporting snake naturality through cohomology models

Source: Stacks Project, homology.tex Tags 0117 and 08N7
(blueprint: lem-pur-support-snake-model-naturality).
-/

@[expose] public section
set_option autoImplicit false
universe v u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Three graded objects and the three arrows of a localization sequence.
Source: Stacks Tag 0117 (blueprint: lem-pur-support-snake-model-naturality). -/
structure SupportHomologyRow (D : Type u) [Category.{v} D] where
  obj₁ : ℤ → D
  obj₂ : ℤ → D
  obj₃ : ℤ → D
  f : ∀ q, obj₁ q ⟶ obj₂ q
  g : ∀ q, obj₂ q ⟶ obj₃ q
  δ : ∀ q, obj₃ q ⟶ obj₁ (q + 1)

/-- An explicit short exact cochain model, with the boundary normalization included.
Source: Stacks Tag 0117 (blueprint: lem-pur-support-snake-model-naturality). -/
structure SupportHomologyRowModel {D : Type u} [Category.{v} D] [Abelian D]
    (R : SupportHomologyRow D) where
  S : ShortComplex (CochainComplex D ℤ)
  shortExact : S.ShortExact
  e₁ : ∀ q, S.X₁.homology q ≅ R.obj₁ q
  e₂ : ∀ q, S.X₂.homology q ≅ R.obj₂ q
  e₃ : ∀ q, S.X₃.homology q ≅ R.obj₃ q
  f_comm : ∀ q, HomologicalComplex.homologyMap S.f q ≫ (e₂ q).hom =
    (e₁ q).hom ≫ R.f q
  g_comm : ∀ q, HomologicalComplex.homologyMap S.g q ≫ (e₃ q).hom =
    (e₂ q).hom ≫ R.g q
  δ_comm : ∀ q, shortExact.δ q (q + 1) rfl ≫ (e₁ (q + 1)).hom =
    (e₃ q).hom ≫ R.δ q

/-- A cochain morphism realizing three specified graded comparison maps.
Source: Stacks Tag 08N7 (blueprint: lem-pur-support-snake-model-naturality). -/
structure SupportComparisonSnakeModel {D : Type u} [Category.{v} D] [Abelian D]
    (R R' : SupportHomologyRow D)
    (c₁ : ∀ q, R.obj₁ q ⟶ R'.obj₁ q)
    (c₂ : ∀ q, R.obj₂ q ⟶ R'.obj₂ q)
    (c₃ : ∀ q, R.obj₃ q ⟶ R'.obj₃ q) where
  left : SupportHomologyRowModel R
  right : SupportHomologyRowModel R'
  φ : left.S ⟶ right.S
  comm₁ : ∀ q, HomologicalComplex.homologyMap φ.τ₁ q ≫ (right.e₁ q).hom =
    (left.e₁ q).hom ≫ c₁ q
  comm₂ : ∀ q, HomologicalComplex.homologyMap φ.τ₂ q ≫ (right.e₂ q).hom =
    (left.e₂ q).hom ≫ c₂ q
  comm₃ : ∀ q, HomologicalComplex.homologyMap φ.τ₃ q ≫ (right.e₃ q).hom =
    (left.e₃ q).hom ≫ c₃ q

namespace SupportComparisonSnakeModel
variable {D : Type u} [Category.{v} D] [Abelian D]
  {R R' : SupportHomologyRow D}
  {c₁ : ∀ q, R.obj₁ q ⟶ R'.obj₁ q}
  {c₂ : ∀ q, R.obj₂ q ⟶ R'.obj₂ q}
  {c₃ : ∀ q, R.obj₃ q ⟶ R'.obj₃ q}
  (M : SupportComparisonSnakeModel R R' c₁ c₂ c₃)

include M

/-- Forgetting supports commutes after transport from the complex model.
Source: Stacks Tag 0117 (blueprint: lem-pur-support-snake-model-naturality). -/
theorem f_naturality (q : ℤ) : R.f q ≫ c₂ q = c₁ q ≫ R'.f q := by
  apply (cancel_epi (M.left.e₁ q).hom).mp
  calc
    (M.left.e₁ q).hom ≫ R.f q ≫ c₂ q =
        HomologicalComplex.homologyMap M.left.S.f q ≫
          HomologicalComplex.homologyMap M.φ.τ₂ q ≫ (M.right.e₂ q).hom := by
      rw [← Category.assoc, ← M.left.f_comm, Category.assoc, M.comm₂]
    _ = HomologicalComplex.homologyMap M.φ.τ₁ q ≫
          HomologicalComplex.homologyMap M.right.S.f q ≫ (M.right.e₂ q).hom := by
      simp only [← Category.assoc, ← HomologicalComplex.homologyMap_comp, M.φ.comm₁₂]
    _ = (M.left.e₁ q).hom ≫ c₁ q ≫ R'.f q := by
      rw [M.right.f_comm, ← Category.assoc, M.comm₁, Category.assoc]

/-- Restriction commutes after transport from the complex model.
Source: Stacks Tag 0117 (blueprint: lem-pur-support-snake-model-naturality). -/
theorem g_naturality (q : ℤ) : R.g q ≫ c₃ q = c₂ q ≫ R'.g q := by
  apply (cancel_epi (M.left.e₂ q).hom).mp
  calc
    (M.left.e₂ q).hom ≫ R.g q ≫ c₃ q =
        HomologicalComplex.homologyMap M.left.S.g q ≫
          HomologicalComplex.homologyMap M.φ.τ₃ q ≫ (M.right.e₃ q).hom := by
      rw [← Category.assoc, ← M.left.g_comm, Category.assoc, M.comm₃]
    _ = HomologicalComplex.homologyMap M.φ.τ₂ q ≫
          HomologicalComplex.homologyMap M.right.S.g q ≫ (M.right.e₃ q).hom := by
      simp only [← Category.assoc, ← HomologicalComplex.homologyMap_comp, M.φ.comm₂₃]
    _ = (M.left.e₂ q).hom ≫ c₂ q ≫ R'.g q := by
      rw [M.right.g_comm, ← Category.assoc, M.comm₂, Category.assoc]

/-- The snake boundary commutes with the same sign after transport.
Source: Stacks Tag 08N7 (blueprint: lem-pur-support-snake-model-naturality). -/
theorem δ_naturality (q : ℤ) : R.δ q ≫ c₁ (q + 1) = c₃ q ≫ R'.δ q := by
  apply (cancel_epi (M.left.e₃ q).hom).mp
  calc
    (M.left.e₃ q).hom ≫ R.δ q ≫ c₁ (q + 1) =
        M.left.shortExact.δ q (q + 1) rfl ≫
          HomologicalComplex.homologyMap M.φ.τ₁ (q + 1) ≫
            (M.right.e₁ (q + 1)).hom := by
      rw [← Category.assoc, ← M.left.δ_comm, Category.assoc, M.comm₁]
    _ = HomologicalComplex.homologyMap M.φ.τ₃ q ≫
          M.right.shortExact.δ q (q + 1) rfl ≫ (M.right.e₁ (q + 1)).hom := by
      rw [← Category.assoc,
        HomologicalComplex.HomologySequence.δ_naturality M.φ
          M.left.shortExact M.right.shortExact q (q + 1) rfl, Category.assoc]
    _ = (M.left.e₃ q).hom ≫ c₃ q ≫ R'.δ q := by
      rw [M.right.δ_comm, ← Category.assoc, M.comm₃, Category.assoc]

end SupportComparisonSnakeModel
end AlgebraicGeometry
