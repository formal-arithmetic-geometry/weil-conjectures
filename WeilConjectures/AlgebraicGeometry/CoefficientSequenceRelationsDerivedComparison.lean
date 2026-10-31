/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientSequenceCoinducedComplexes
import WeilConjectures.AlgebraicGeometry.CoefficientSequenceCanonicalComparisonsIso
import WeilConjectures.AlgebraicGeometry.CoefficientSequenceCanonicalCompatibility
import WeilConjectures.AlgebraicGeometry.CoefficientSequenceCoinducedShortExact

/-! # Derived comparison for the relation coinduced product

Source: Stacks Tags 0941 and 079P.
(blueprint: lem-coef-sequence-relations-derived-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  Opposite AlgebraicGeometry
namespace WeilConjectures.CoefficientCoinduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})

set_option maxHeartbeats 2000000 in
-- Elaborate the explicit coefficient comparison triangle.
/--
Given any first-product comparison `a` satisfying the augmentation equation, the
ordinary relation product localizes to the specified derived relation product and
the localized difference agrees with `a` followed by the derived difference.
Source: Stacks Tags 0941 and 079P.
(blueprint: lem-coef-sequence-relations-derived-comparison).

Proof: first for the comparison `a₀` built from K-injective resolutions of the
`ev_n K` (as in `complexProduct_derivedComparison`). Resolve each
`Res(ev_{n+1} K)` independently by a K-injective complex; exact coinduction keeps
it K-injective and the locally finite product of these coinduced replacements is a
quasi-isomorphic K-injective model of the derived relation product, which gives
`b₀`. Projected to the factor n and transposed by the derived adjunction, both
`Q(diff) ≫ b₀` and `a₀ ≫ derivedDifference` become the same difference of the two
adjacent composites (localized transition, naturality of the evaluation and
restriction factorizations); products detect equality. For an arbitrary `a` with
the augmentation equation put `φ = a₀⁻¹ ≫ a`, so `derivedAugmentation ≫ φ =
derivedAugmentation`. Localizing the short exact sequence
`complexSequence_shortExact` and transporting by `(1, a₀, b₀)` makes
`(derivedAugmentation, derivedDifference)` the first two maps of a distinguished
triangle, so `φ - 1 = derivedDifference ≫ χ` for some `χ`. Then
`b = b₀ ≫ (1 + χ ≫ derivedDifference)` is an isomorphism (its inverse exists since
`1 + derivedDifference ≫ χ = φ` is invertible) and
`Q(diff) ≫ b = a₀ ≫ derivedDifference ≫ (1 + χ ≫ derivedDifference)
  = a₀ ≫ φ ≫ derivedDifference = a ≫ derivedDifference`. -/
theorem complexRelations_derivedComparison
    (K : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (a : DerivedCategory.Q.obj (complexProduct l E W K) ≅
      derivedProduct l E W (DerivedCategory.Q.obj K))
    (ha : DerivedCategory.Q.map (complexAugmentation l E W K) ≫ a.hom =
      derivedAugmentation l E W (DerivedCategory.Q.obj K)) :
    ∃ (b : DerivedCategory.Q.obj (complexRelations l E W K) ≅
        derivedRelations l E W (DerivedCategory.Q.obj K)),
      DerivedCategory.Q.map (complexDifference l E W K) ≫ b.hom =
        a.hom ≫ derivedDifference l E W (DerivedCategory.Q.obj K) := by
  obtain ⟨h₁, h₂⟩ := canonicalComparisons_isIso l E W K
  let a₀ := asIso (canonicalProductComparison l E W K)
  let b₀ := asIso (canonicalRelationsComparison l E W K)
  obtain ⟨ha₀, hb₀⟩ := canonicalComparisons_compatible l E W K
  let hS := complexSequence_shortExact l E W K
  let δ := b₀.inv ≫ DerivedCategory.triangleOfSESδ hS
  let T := Triangle.mk
    (derivedAugmentation l E W (DerivedCategory.Q.obj K))
    (derivedDifference l E W (DerivedCategory.Q.obj K)) δ
  have hT : T ∈ distTriang (coefficientSequenceDerived l E W) := by
    apply (Pretriangulated.distinguished_iff_of_iso
      (Triangle.isoMk (DerivedCategory.triangleOfSES hS) T (Iso.refl _) a₀ b₀
        (by rw [Iso.refl_hom, Category.id_comp, Triangle.mk_mor₁]; exact ha₀)
        (by rw [Triangle.mk_mor₂]; exact hb₀) (by simp [T, δ]))).mp
    exact DerivedCategory.triangleOfSES_distinguished hS
  let e := Pretriangulated.isoTriangleOfIso₁₂ (DerivedCategory.triangleOfSES hS) T
    (DerivedCategory.triangleOfSES_distinguished hS) hT (Iso.refl _) a
    (by rw [Iso.refl_hom, Category.id_comp]; exact ha)
  refine ⟨Triangle.π₃.mapIso e, ?_⟩
  have h := e.hom.comm₂
  change DerivedCategory.Q.map (complexDifference l E W K) ≫ e.hom.hom₃ =
    e.hom.hom₂ ≫ derivedDifference l E W (DerivedCategory.Q.obj K) at h
  have he : e.hom.hom₂ = a.hom :=
    Pretriangulated.isoTriangleOfIso₁₂_hom_hom₂ _ _ _ _ _ _ _
  rw [he] at h
  exact h

end WeilConjectures.CoefficientCoinduction
