/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.CondensedCoefficientTowers
/-! # Constructible and normalized condensed coefficient towers
Source: sk-def-sp-normalized-towers (blueprint: sk-def-sp-normalized-towers).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Uniform cohomological and Tor bounds on constructible finite levels, with no normalization.
Source: sk-def-sp-normalized-towers (blueprint: sk-lem-sp-tower). -/
def ConstructibleTowers : ObjectProperty (DerivedTowers l E T) := fun C ↦
  (∀ n, constantModelBoundedConstructible (finiteRing l E n) T
    ((evaluation l E T n).obj C)) ∧
  ∃ a b c d : ℤ, a ≤ b ∧ c ≤ d ∧ ∀ n : ℕ,
    DerivedCategory.torAmplitudeIn _ c d ((evaluation l E T n).obj C) ∧
    ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj ((evaluation l E T n).obj C))

/-- Constructible towers with uniform bounds, as a full derived subcategory.
Source: sk-def-sp-normalized-towers (blueprint: sk-lem-sp-tower). -/
abbrev CtfTowers := (ConstructibleTowers l E T).FullSubcategory

/-- Normalization uses the adjoints of the actual strict transitions, for all comparable
positive levels, including equal levels. Source: sk-def-sp-normalized-towers
(blueprint: sk-lem-sp-tower). -/
def Normalized (D : Model l E T) : ObjectProperty (DerivedTowers l E T) := fun C ↦
  ConstructibleTowers l E T C ∧ ∀ (m n : ℕ) (h : m ≤ n), IsIso ((D.reduction h).app C)

/-- Full normalized constructible tower subcategory.
Source: sk-def-sp-normalized-towers (blueprint: sk-lem-sp-tower). -/
abbrev NormalizedTowers (D : Model l E T) := (Normalized l E T D).FullSubcategory


end AlgebraicGeometry.ProEtale.CondensedIntegralTower
