/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.DirectImage
public import WeilConjectures.DeligneLaumon.Reduction.MixedStalk
public import WeilConjectures.WeilSheaf.PoincareDuality

/-!
# The weight estimate for smooth proper varieties

Let `X₀` be a proper scheme over the finite field `k₀ = 𝔽_q`, and let `ι : ℚ̄_ℓ → ℂ` be a field
embedding. Deligne's weight estimate for `Rf_!`
(`AlgebraicGeometry.hasDirectImageWeightBound_over_finiteField`) applied to the structure
morphism of `X₀` and the constant Weil sheaf, which is punctually pure of weight `0`, shows that
`H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` has weights at most `i`.

## Main statements

- `AlgebraicGeometry.WeilComplex.proper_compact_coincidence`: `Ra_! ≅ Ra_*` and `H_c^i ≅ Hⁱ` for a
  proper `k₀`-scheme.
- `AlgebraicGeometry.WeilSheaf.isMixedOfWeightsAtMost_toComplex_adicConstant`: the constant Weil
  sheaf, as a Weil complex, is mixed of weights at most `0`; together with
  `AlgebraicGeometry.WeilSheaf.isPunctuallyPureOfWeight_adicConstant` (the constant Weil sheaf is
  punctually pure of weight `0`, `corollary-purity-cohomology-smooth-proper-variety`) this is
  `corollary-purity-cohomology-smooth-proper-variety`
  (`AlgebraicGeometry.WeilSheaf.weightPurity_adicConstant`).
- `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.hasWeightsAtMostOver_globalSections`: a
  Weil sheaf on `Spec k₀` mixed of weights at most `w` has global sections of weights at most `w`.
- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_adicConstant`:
  `H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ)` has weights at most `i`.
- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_cohomology_adicConstant`: `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)`
  has weights at most `i` for `X₀` proper.

The purity of `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for `X₀` smooth and proper
(`AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_cohomology_adicConstant`,
`AlgebraicGeometry.WeilSheaf.purity_smoothProper`, `AlgebraicGeometry.WeilSheaf.deligne_purity`)
is the case of the constant sheaf of the purity theorem for lisse coefficients, in
`WeilConjectures.ZetaFunction.LissePurity`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/- Through `Mathlib.AlgebraicGeometry.Group.Affine`, `Spec k₀` is also an object over itself via
`specOverSpec`; prefer the identity structure `CategoryTheory.instOverClass`. -/
attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]

/-- Proper coincidence: for `Y` proper
over `k₀` with structure morphism `a`, the compactly supported direct image is the ordinary direct
image, `Ra_! K ≅ Ra_* K` (the identity is a compactification of `a`), and hence
`H_c^i(Y ⊗ k̄, K) ≅ Hⁱ(Y ⊗ k̄, K)` Frobenius-equivariantly for every Weil complex `K` and every
`i`. -/
theorem proper_compact_coincidence (K : WeilComplex k₀ l X) :
    Nonempty ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj K ≅
      (derivedLowerStar (X ↘ Spec (CommRingCat.of k₀))).obj K) ∧
    ∀ i : ℤ, Nonempty ((K.compactlySupportedCohomology i).Equiv (K.cohomology i)) :=
  ⟨⟨derivedLowerShriekObjIsoOfIsProper K⟩, nonempty_equiv_compactlySupportedCohomology_cohomology K⟩

end WeilComplex

namespace WeilSheaf

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Blueprint `corollary-purity-cohomology-smooth-proper-variety` (the complex form): the constant
Weil sheaf, viewed as a Weil complex concentrated in degree `0`, is `ι`-mixed of weights at most
`0`: its cohomology sheaf in degree `0` is the constant sheaf, punctually pure of weight `0`, and
the others vanish. -/
theorem isMixedOfWeightsAtMost_toComplex_adicConstant
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (ι : PadicAlgCl l →+* ℂ) :
    (toComplex.obj (adicConstant k₀ l X)).IsMixedOfWeightsAtMost ι 0 := by
  intro b
  by_cases hb : b = 0
  · subst hb
    rw [Int.cast_zero, add_zero, isMixedOfWeightsAtMost_iff_filtrationClosure]
    refine ObjectProperty.prop_of_iso _
      (WeilComplex.homologySheafSingleComplexIso 0 (adicConstant k₀ l X)).symm
      (ObjectProperty.le_filtrationClosure _
        ⟨0, le_rfl, isPunctuallyPureOfWeight_adicConstant (k₀ := k₀) (l := l) (X := X) (ι := ι)⟩)
  · exact isMixedOfWeightsAtMost_of_isZero
      (WeilComplex.isZero_homologySheaf_singleComplex hb _) _

/-- Blueprint `corollary-purity-cohomology-smooth-proper-variety`: the constant Weil sheaf is
`ι`-pure of weight `0`, punctually
(`AlgebraicGeometry.WeilSheaf.isPunctuallyPureOfWeight_adicConstant`), and as a Weil complex it is
mixed of weights at most `0`. -/
theorem weightPurity_adicConstant [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (ι : PadicAlgCl l →+* ℂ) :
    (adicConstant k₀ l X).IsPunctuallyPureOfWeight ι 0 ∧
      (toComplex.obj (adicConstant k₀ l X)).IsMixedOfWeightsAtMost ι 0 :=
  ⟨isPunctuallyPureOfWeight_adicConstant (k₀ := k₀) (l := l) (X := X) (ι := ι),
    isMixedOfWeightsAtMost_toComplex_adicConstant k₀ l X ι⟩

variable {k₀ l} in
/-- A Weil sheaf on `Spec k₀` which is `ι`-mixed of weights at most `w` has global sections of
weights at most `w`: every eigenvalue of the Frobenius on `Γ(Spec k̄, G)` is a local Frobenius
eigenvalue at the unique closed point, of degree one, and the filtration of `G` by punctually
pure sheaves of weights at most `w` bounds it. -/
theorem IsMixedOfWeightsAtMost.hasWeightsAtMostOver_globalSections {ι : PadicAlgCl l →+* ℂ}
    {G : WeilSheaf k₀ l (Spec (CommRingCat.of k₀))} {w : ℝ}
    (hG : G.IsMixedOfWeightsAtMost ι w) :
    G.globalSections.HasWeightsAtMostOver k₀ ι w := by
  intro β hβ
  obtain ⟨x, hx⟩ := exists_hasEigenvalue_stalk_of_hasEigenvalue_globalSections G hβ
  have h := hG.hasWeightsAtMost x _ hx
  have hm := (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2
  have hq : (0 : ℝ) ≤ Nat.card k₀ := Nat.cast_nonneg _
  rw [map_pow, norm_pow, Scheme.Hom.residueCard, Nat.cast_pow, ← Real.rpow_natCast_mul hq,
    mul_comm, Real.rpow_mul_natCast hq] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.rpow_nonneg hq _) hm).1 h

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Clause (2) of `corollary-purity-cohomology-smooth-proper-variety` and of
`corollary-purity-cohomology-smooth-proper-variety`: for a separated `k₀`-scheme `X₀` of finite
type, `H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ)` is `ι`-mixed of weights at most `i`: every eigenvalue `α` of the
geometric Frobenius satisfies `|ι α| ≤ q^{i/2}`. This is the Deligne–Laumon estimate for the
structure morphism of `X₀` and the constant Weil sheaf, mixed of weights at most `0`. -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_adicConstant (ι : PadicAlgCl l →+* ℂ)
    (i : ℤ) :
    ((adicConstant k₀ l X).compactlySupportedCohomology i).HasWeightsAtMostOver k₀ ι i := by
  have h := (isMixedOfWeightsAtMost_toComplex_adicConstant k₀ l X ι).derivedLowerShriek
    (X ↘ Spec (CommRingCat.of k₀)) i
  rw [zero_add] at h
  exact IsMixedOfWeightsAtMost.hasWeightsAtMostOver_globalSections h

end WeilSheaf

namespace WeilSheaf

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]

/-- For `X₀` proper over `k₀`, `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` has weights at most `i`: it is isomorphic to
`H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ)`. -/
theorem hasWeightsAtMostOver_cohomology_adicConstant (ι : PadicAlgCl l →+* ℂ) (i : ℤ) :
    ((adicConstant k₀ l X).cohomology i).HasWeightsAtMostOver k₀ ι i := by
  obtain ⟨e⟩ := WeilComplex.nonempty_equiv_compactlySupportedCohomology_cohomology
    (toComplex.obj (adicConstant k₀ l X)) i
  exact fun α hα ↦ hasWeightsAtMostOver_compactlySupportedCohomology_adicConstant k₀ l X ι i α
    (FrobeniusModule.hasEigenvalue_of_surjective e.toLinearEquiv.toLinearMap e.map_frobenius
      e.toLinearEquiv.surjective hα)

end WeilSheaf

end AlgebraicGeometry
