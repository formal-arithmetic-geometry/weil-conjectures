/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.TowerPreservation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProperDirectImageFiniteness

/-!
# Amplification for proper cartesian squares

For a cartesian square with `f` (hence `f'`) proper, whose geometric fibres have dimension at
most `e`, and coefficient quotients `P_n = A ⧸ Iⁿ` killed by a power of an integer `N`
invertible on the base, the finite-level amplification `AMP(□; 2e)` holds
(`AlgebraicGeometry.ProEtale.finiteLevelAmplification_of_isProper`, the `AMP` part of blueprint
`thm-weil-pbc-amplification-proper`). For `I = (ϖ)` with `ϖ` a nonzerodivisor, the witness
compatibility `WIT(□)` and the tower preservation `TOW(□)` hold as well
(`AlgebraicGeometry.ProEtale.amplification_of_isProper`), and the four functors preserve the
bounded constructible complete categories `Dᵇc(-_proét, A)`
(`AlgebraicGeometry.ProEtale.boundedConstructibleCompleteIn_of_isProper`, blueprint
`prop-weil-pbc-preservation-constructible`).

As for `thm-weil-pbc-direct-image-finiteness-proper`
(`AlgebraicGeometry.ProEtale.directImageFiniteness_of_isProper`), the bases are assumed of finite
type over a field `k` in which `N` is invertible.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The geometric fibres of the base change `f'` of `f` along `g` are geometric fibres of `f`:
`X' ×_{Y'} Spec Ω ≅ X ×_Y Spec Ω`. -/
lemma topologicalKrullDim_pullback_le_of_isPullback {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g) (e : ℕ)
    (he : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s' : Spec (.of Ω) ⟶ Y') :
    topologicalKrullDim (pullback f' s' : Scheme.{u}) ≤ (e : WithBot ℕ∞) := by
  have big : IsPullback (pullback.fst f' s' ≫ g') (pullback.snd f' s') f (s' ≫ g) :=
    (IsPullback.of_hasPullback f' s').paste_horiz sq
  rw [IsHomeomorph.topologicalKrullDim_eq _ (homeoOfIso big.isoPullback).isHomeomorph]
  exact he Ω (s' ≫ g)

/-- If an integer `N` lies in `I` and is invertible in `k`, then the exponent of every quotient
`A ⧸ Iⁿ` (`n ≥ 1`) is invertible on `Spec k`. -/
lemma hasInvertibleExponent_quotient_pow {A : Type (u + 1)} [CommRing A] {I : Ideal A}
    {k : Type u} [Field k] {N : ℕ} (hN : 0 < N) (hNI : (N : A) ∈ I) (hNk : IsUnit (N : k))
    (n : ℕ) : HasInvertibleExponent (A ⧸ I ^ n) (Spec (.of k)) := by
  refine ⟨N ^ n, pow_pos hN n, ?_, ?_⟩
  · rw [Nat.cast_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hNI n
  · have := (hNk.pow n).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    simpa using this

variable (A : Type (u + 1)) [CommRing A] (I : Ideal A)

/-- Blueprint `thm-weil-pbc-amplification-proper`, the condition `AMP(□; 2e)`: let `□` be a
cartesian square with `f` proper and `Y`, `Y'` of finite type over a field `k`, the geometric
fibres of `f` of dimension at most `e`, and suppose an integer `N > 0` lies in `I` (i.e.
annihilates `A ⧸ I`) and is invertible in `k`, every `A ⧸ Iⁿ` being finite. Then `AMP(□; 2e)`
holds: `FIN(f, P_n; 2e)` and `FIN(f', P_n; 2e)` by the finiteness of proper direct images
(`thm-weil-pbc-direct-image-finiteness-proper`; the geometric fibres of `f'` are geometric fibres
of `f`), the pullback clause by `lem-weil-pbc-pullback-preserves-bounded-constructible`. -/
theorem finiteLevelAmplification_of_isProper {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g) [IsProper f]
    {k : Type u} [Field k] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (aY' : Y' ⟶ Spec (.of k)) [LocallyOfFiniteType aY'] [QuasiCompact aY']
    [∀ n, Finite (A ⧸ I ^ n)] {N : ℕ} (hN : 0 < N) (hNI : (N : A) ∈ I)
    (hNk : IsUnit (N : k)) (e : ℕ)
    (he : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞)) :
    FiniteLevelAmplification A I sq (2 * e) := by
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) sq.flip inferInstance
  refine FiniteLevelAmplification.of_directImageFiniteness sq (fun n _ ↦ ?_) (fun n _ ↦ ?_)
  · have := hasInvertibleExponent_quotient_pow hN hNI hNk n
    exact directImageFiniteness_of_isProper f aY e he
  · have := hasInvertibleExponent_quotient_pow hN hNI hNk n
    exact directImageFiniteness_of_isProper f' aY' e
      (topologicalKrullDim_pullback_le_of_isPullback sq e he)


variable {A I}

section Tower

variable {ϖ : A} (hϖ : ϖ ∈ nonZeroDivisors A) (hI : I = Ideal.span {ϖ}) [∀ n, Finite (A ⧸ I ^ n)]

include hϖ hI in
/-- For `f` proper with geometric fibres of dimension at most `e` over a base of finite type
over a field `k` in which an integer `N ∈ I` is invertible, the direct image `Rf_*` preserves
constructible towers with shift `2e`: for a tower with levels `M_n ∈ D_c^[a, b](X, A ⧸ Iⁿ)`,
`Rf_* (Res M_n) ≅ Res (Rf_* M_n)`
(`AlgebraicGeometry.ProEtale.derivedRestrictScalarsRightDerivedLowerStarIso`)
lies in `D_c^[a, b + 2e](Y, A)` by the finiteness of proper direct images over `A ⧸ Iⁿ`
(`thm-weil-pbc-direct-image-finiteness-proper`). -/
theorem preservesConstructibleTowers_rightDerivedLowerStar_of_isProper {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] {k : Type u} [Field k] (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] {N : ℕ} (hN : 0 < N) (hNI : (N : A) ∈ I)
    (hNk : IsUnit (N : k)) (e : ℕ)
    (he : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞)) :
    PreservesConstructibleTowers I (R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f)) (2 * e) := by
  refine preservesConstructibleTowers_of_linear hϖ hI _ _ fun M a b hM n ↦ ?_
  have := hasInvertibleExponent_quotient_pow hN hNI hNk n
  have hfin := (directImageFiniteness_of_isProper (Λ := A ⧸ I ^ n) f aY e he).
    boundedConstructible_rightDerivedLowerStar (hM n).1 (hM n).2
  exact (DerivedCategory.constructibleIn _ Y a (b + (2 * e : ℕ))).prop_of_iso
    (derivedRestrictScalarsRightDerivedLowerStarIso (Ideal.Quotient.mk (I ^ n)) f (M.obj n)
      (hM n).1.bounded.1)
    (DerivedCategory.constructibleIn_derivedRestrictScalars_obj (I ^ n) hfin)

include hϖ hI in
/-- The derived pullback `Lg^*` preserves constructible towers (with shift `0`): the
restrictions of scalars `Res M_n` of the levels lie in `D_c^[a, b](Y, A)`, and `Lg^*`
preserves `D_c^[a, b]` (`lem-weil-pbc-pullback-preserves-bounded-constructible`). -/
theorem preservesConstructibleTowers_leftDerivedUpperStar {X Y : Scheme.{u}} (g : X ⟶ Y) :
    PreservesConstructibleTowers I (L(ProEtale.upperStar (ModuleCat.{u + 1} A) g)) 0 := by
  refine preservesConstructibleTowers_of_linear hϖ hI _ _ fun M a b hM n ↦ ?_
  have h := DerivedCategory.constructibleIn_derivedRestrictScalars_obj (I ^ n) (hM n)
  simpa using (⟨boundedConstructible_leftDerivedUpperStar g h.1,
    homologyConcentratedIn_leftDerivedUpperStar g h.2⟩ :
      DerivedCategory.constructibleIn _ X a b _)

include hϖ hI in
/-- Blueprint `thm-weil-pbc-amplification-proper`, the condition `TOW(□)`: under the hypotheses
of `AlgebraicGeometry.ProEtale.finiteLevelAmplification_of_isProper`, the four functors
preserve uniformly bounded constructible towers, with amplitudes `[a, b + 2e]` for the direct
images and `[a, b]` for the pullbacks. -/
theorem towerPreservation_of_isProper {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g) [IsProper f]
    {k : Type u} [Field k] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (aY' : Y' ⟶ Spec (.of k)) [LocallyOfFiniteType aY'] [QuasiCompact aY']
    {N : ℕ} (hN : 0 < N) (hNI : (N : A) ∈ I) (hNk : IsUnit (N : k)) (e : ℕ)
    (he : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞)) :
    TowerPreservation A I sq (2 * e) := by
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) sq.flip inferInstance
  exact
    { lowerStar := preservesConstructibleTowers_rightDerivedLowerStar_of_isProper hϖ hI f aY hN
        hNI hNk e he
      lowerStar' := preservesConstructibleTowers_rightDerivedLowerStar_of_isProper hϖ hI f' aY'
        hN hNI hNk e (topologicalKrullDim_pullback_le_of_isPullback sq e he)
      upperStar := preservesConstructibleTowers_leftDerivedUpperStar hϖ hI g
      upperStar' := preservesConstructibleTowers_leftDerivedUpperStar hϖ hI g' }

include hϖ hI in
/-- Blueprint `thm-weil-pbc-amplification-proper`: Amplification for proper base-change squares.

Let `□` be a cartesian square with `f` proper and `Y`, `Y'` of finite type over a field `k`,
the geometric fibres of `f` of dimension at most `e`, let `I = (ϖ)` for a nonzerodivisor `ϖ`
with every `A ⧸ Iⁿ` finite, and suppose an integer `N > 0` lies in `I` and is invertible in
`k`. Then `AMP(□; 2e)` (`AlgebraicGeometry.ProEtale.finiteLevelAmplification_of_isProper`),
`WIT(□)` (`AlgebraicGeometry.ProEtale.witnessCompatibility_of_isPullback`) and `TOW(□)`
(`AlgebraicGeometry.ProEtale.towerPreservation_of_isProper`) hold. -/
theorem amplification_of_isProper {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g) [IsProper f]
    {k : Type u} [Field k] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (aY' : Y' ⟶ Spec (.of k)) [LocallyOfFiniteType aY'] [QuasiCompact aY']
    {N : ℕ} (hN : 0 < N) (hNI : (N : A) ∈ I) (hNk : IsUnit (N : k)) (e : ℕ)
    (he : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞)) :
    FiniteLevelAmplification A I sq (2 * e) ∧ WitnessCompatibility A I sq ∧
      TowerPreservation A I sq (2 * e) := by
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) sq.flip inferInstance
  exact ⟨finiteLevelAmplification_of_isProper A I sq aY aY' hN hNI hNk e he,
    witnessCompatibility_of_isPullback hϖ hI sq,
    towerPreservation_of_isProper hϖ hI sq aY aY' hN hNI hNk e he⟩

include hϖ hI in
/-- Blueprint `prop-weil-pbc-preservation-constructible`: Preservation before constructible
restriction.

Under the hypotheses of `AlgebraicGeometry.ProEtale.amplification_of_isProper`, for every
`K ∈ Dᵇc(X_proét, A)` whose reductions have the common interval `[a, b]`:
`Rf_* K ∈ Dᵇc(Y_proét, A)`, the completed pullback `Lg^*_comp Rf_* K` (any homotopy limit of the
reductions of `Lg^* Rf_* K`) lies in `Dᵇc(Y'_proét, A)`, the completed pullback `Lg'^*_comp K`
lies in `Dᵇc(X'_proét, A)` and `Rf'_* Lg'^*_comp K ∈ Dᵇc(Y'_proét, A)`; the pullback
`Lg'^*_comp K` has reduction amplitude `[a, b]`, the other three objects reduction amplitude
contained in `[a, b + 2e]`. By `thm-weil-pbc-amplification-proper` this is the formal argument
`AlgebraicGeometry.ProEtale.boundedConstructibleCompleteIn_of_witnessCompatibility`. -/
theorem boundedConstructibleCompleteIn_of_isProper {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g) [IsProper f]
    {k : Type u} [Field k] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (aY' : Y' ⟶ Spec (.of k)) [LocallyOfFiniteType aY'] [QuasiCompact aY']
    {N : ℕ} (hN : 0 < N) (hNI : (N : A) ∈ I) (hNk : IsUnit (N : k)) (e : ℕ)
    (he : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    {a b : ℤ} (hK : DerivedCategory.boundedConstructibleCompleteIn I X a b K) :
    DerivedCategory.boundedConstructibleCompleteIn I Y a (b + (2 * e : ℕ))
        ((R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f)).obj K) ∧
      (∀ {cY : Cone (_root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology Y') I
          ((L(ProEtale.upperStar (ModuleCat.{u + 1} A) g)).obj
            ((R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f)).obj K)))},
        IsHomotopyLimit cY →
          DerivedCategory.boundedConstructibleCompleteIn I Y' a (b + (2 * e : ℕ)) cY.pt) ∧
      ∀ {cX : Cone (_root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology X') I
          ((L(ProEtale.upperStar (ModuleCat.{u + 1} A) g')).obj K))},
        IsHomotopyLimit cX → DerivedCategory.boundedConstructibleCompleteIn I X' a b cX.pt ∧
          DerivedCategory.boundedConstructibleCompleteIn I Y' a (b + (2 * e : ℕ))
            ((R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f')).obj cX.pt) := by
  obtain ⟨-, hW, hT⟩ := amplification_of_isProper hϖ hI sq aY aY' hN hNI hNk e he
  exact boundedConstructibleCompleteIn_of_witnessCompatibility hϖ hI hW hT hK

end Tower
end AlgebraicGeometry.ProEtale
