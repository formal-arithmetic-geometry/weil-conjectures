/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.Amplification
public import WeilConjectures.SixFunctors.ProEtale.Derived.ProperDirectImageFiniteness

/-!
# Amplification for proper cartesian squares

For a cartesian square with `f` (hence `f'`) proper, whose geometric fibres have dimension at
most `e`, and coefficient quotients `P_n = A ⧸ Iⁿ` killed by a power of an integer `N`
invertible on the base, the finite-level amplification `AMP(□; 2e)` holds
(`AlgebraicGeometry.ProEtale.finiteLevelAmplification_of_isProper`, the `AMP` part of blueprint
`thm-weil-pbc-amplification-proper`).

As for `thm-weil-pbc-direct-image-finiteness-proper`
(`AlgebraicGeometry.ProEtale.directImageFiniteness_of_isProper`), the bases are assumed of finite
type over a field `k` in which `N` is invertible.
-/

@[expose] public section

universe u

open CategoryTheory Limits

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

end AlgebraicGeometry.ProEtale
