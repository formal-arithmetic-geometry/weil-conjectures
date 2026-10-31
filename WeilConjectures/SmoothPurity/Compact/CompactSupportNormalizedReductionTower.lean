/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
import WeilConjectures.SmoothPurity.Compact.CompactSupportNormalizedReductionTowerData
import WeilConjectures.SmoothPurity.Compact.CompactSupportNormalizedReductionTowerBounds

/-! # Normalization of the finite compact-support tower -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

set_option linter.unusedVariables false in
/-- The finite compact-support tower of an integral constructible input admits a
normalized DVR realization, with a common constructible cohomological bound.
No inverse limit, its projections, or their reduction comparisons occur here.
Source: current blueprint lem-fix-operation-reduction.proof.md, compact-support paragraph;
Bhatt--Scholze Lemmas 6.7.7 and 6.8.14; Stacks Tags 08J9 and 0FPT.
(blueprint: lem-sf-compact-support-normalized-reduction-tower).

Proof: choose a flat-term K-flat resolution of K. Its quotient complexes form a
normalized tower: the two-term free resolutions of the positive DVR quotients
identify every iterated derived reduction with the corresponding quotient level.
Apply extension by zero followed by proper derived direct image to these levels.
Extension by zero is exact and its coefficient comparison is the sectionwise tensor
unit. For proper direct image use the projection formula for the two-term finite free
quotient resolution. On representatives these comparisons are the scalar-adjunction
mates and commute with all quotient maps, including identities and composites.
The coherent tower substitution construction therefore produces T and the level
isomorphisms a; its adjacent transition square is exactly the displayed equality.
Constructibility of finite compact supports gives constructible levels. The uniform
bound on the input reductions, exactness of extension by zero, and the finite
cohomological dimension bound for this fixed proper finite-type map give one interval
containing the cohomological support of every level. This construction needs only
invertibility of l over K₀. D and hl index the abstract normalized coefficient calculus;
no scheme is assumed to be over D. The argument includes exponent one, the zero input
and the empty scheme. It never asserts flatness of a quotient-ring map. -/
theorem compactSupport_normalizedReductionTower
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (K₀ : Type u) [Field K₀] (hl₀ : IsUnit (l : K₀))
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))]
    [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
    [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource l E X))
    (hK : sfIntegralConstructible l E X K)
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    ∃ (T : NormalizedDVRTower l E Y D hl)
      (a : ∀ n : ℕ, T.M n ≅
        (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
          ((scalarReductionDerivedExtension l E X n).obj K)),
      (∀ n : ℕ,
        (normalizedDVRTowerTransition l E Y D hl n.le_succ).app T.tower ≫
            (T.evaluationIso n ≪≫
              (scalarReductionDerivedRestriction l E Y n).mapIso (a n)).hom =
          (T.evaluationIso (n + 1) ≪≫
              (scalarReductionDerivedRestriction l E Y (n + 1)).mapIso (a (n + 1))).hom ≫
            sfCompactSupportTransition l E c K n) ∧
      ∃ b₀ b₁ : ℤ, b₀ ≤ b₁ ∧ ∀ n : ℕ,
        intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) Y
          ((sfAmbientCompactSupportCandidate
            (Padic.coefficientExtensionRing l E (n + 1)) c).obj
              ((scalarReductionDerivedExtension l E X n).obj K)) ∧
        proEtaleCohomologicalSupport
          ((sfAmbientCompactSupportCandidate
            (Padic.coefficientExtensionRing l E (n + 1)) c).obj
              ((scalarReductionDerivedExtension l E X n).obj K)) ⊆ Set.Icc b₀ b₁ := by
  obtain ⟨T, a, ht⟩ := compactSupport_normalizedReductionTower_data l E K₀ hl₀ c K hK D hl
  obtain ⟨b₀, b₁, hb, hbounds⟩ :=
    compactSupport_normalizedReductionTower_bounds l E K₀ hl₀ c K hK D hl
  exact ⟨T, a, ht, b₀, b₁, hb, hbounds⟩

end WeilConjectures
