/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Selected finite relative affine presentations

Source: the blueprint of the Weil conjectures, Nagata compactification,
`sk-prop-nagata-sketch-approximation`
(blueprint: def-nagata-relative-finite-affine-presentation).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The selected finite affine charts, their finite algebra presentations, and basic-open
overlap comparisons for a morphism of finite presentation over a qcqs base. The index types
may be empty, as required for the empty scheme. The chosen data are allowed to depend on
previously prescribed base charts (blueprint: def-nagata-relative-finite-affine-presentation). -/
structure RelativeFiniteAffinePresentation {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f] where
  baseIndex : Type u
  finiteBase : Finite baseIndex
  base : baseIndex → S.Opens
  baseAffine : ∀ a, IsAffineOpen (base a)
  baseCovers : ⨆ a, base a = ⊤
  chartIndex : baseIndex → Type u
  finiteCharts : ∀ a, Finite (chartIndex a)
  chart : ∀ a, chartIndex a → X.Opens
  chartAffine : ∀ a b, IsAffineOpen (chart a b)
  chartOver : ∀ a b, chart a b ≤ f ⁻¹ᵁ base a
  chartCovers : ∀ a, ⨆ b, chart a b = f ⁻¹ᵁ base a
  presentation : ∀ a b, Σ n : ℕ, Σ r : ℕ,
    @Algebra.Presentation (Γ(S, base a)) (Γ(X, chart a b)) (Fin n) (Fin r)
      _ _ (f.appLE (base a) (chart a b) (chartOver a b)).hom.toAlgebra
  overlapIndex : (Σ a, chartIndex a) → (Σ a, chartIndex a) → Type u
  finiteOverlaps : ∀ c d, Finite (overlapIndex c d)
  leftSection : ∀ c d, overlapIndex c d → Γ(X, chart c.1 c.2)
  rightSection : ∀ c d, overlapIndex c d → Γ(X, chart d.1 d.2)
  basicAgree : ∀ c d k,
    X.basicOpen (leftSection c d k) = X.basicOpen (rightSection c d k)
  overlapCovers : ∀ c d,
    ⨆ k, X.basicOpen (leftSection c d k) = chart c.1 c.2 ⊓ chart d.1 d.2
  comparison : ∀ c d k,
    Localization.Away (leftSection c d k) ≃+*
      Localization.Away (rightSection c d k)
  comparisonIsRestriction : ∀ c d k, comparison c d k = by
    let l := leftSection c d k
    let r := rightSection c d k
    letI := (chartAffine c.1 c.2).isLocalization_basicOpen l
    letI := (chartAffine d.1 d.2).isLocalization_basicOpen r
    let leftIso := (IsLocalization.algEquiv (Submonoid.powers l)
      (Localization.Away l) Γ(X, X.basicOpen l)).toRingEquiv
    let rightIso := (IsLocalization.algEquiv (Submonoid.powers r)
      (Localization.Away r) Γ(X, X.basicOpen r)).toRingEquiv
    let middle : Γ(X, X.basicOpen l) ≃+* Γ(X, X.basicOpen r) :=
      RingEquiv.cast (R := fun U : X.Opens => Γ(X, U)) (basicAgree c d k)
    exact leftIso.trans (middle.trans rightIso.symm)

end AlgebraicGeometry
