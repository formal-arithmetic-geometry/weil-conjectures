/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module

public import Sheaf.Paper.FiniteLevelAmplification
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.Paper.ProperDirectImageFiniteness
import Sheaf.AlgebraicGeometry.PullbackBoundedConstructible

/-! # Finite amplification for a proper square

This is the finite-coefficient part (a) of the proper amplification assembly.
Source: blueprint main-20261015, proper base change
(blueprint: lem-weil-pbc-finite-amplification-proper).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

private theorem quotient_order_isUnit
    {T : Scheme.{u}} {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (N : ℕ) (h : ∀ a : A ⧸ I, N • a = 0)
    (hInvert : ∀ x : T, IsUnit (N : T.presheaf.stalk x))
    (n : ℕ) (a : A ⧸ I ^ n) (x : T) :
    IsUnit (addOrderOf a : T.presheaf.stalk x) := by
  have hmem : (N : A) ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [nsmul_eq_mul, mul_one, map_natCast] using h 1
  have hz : (N : A ⧸ I ^ n) ^ n = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [map_pow, map_natCast] using Ideal.pow_mem_pow hmem n
  have hann : N ^ n • a = 0 := by
    rw [nsmul_eq_mul, Nat.cast_pow, hz, zero_mul]
  apply isUnit_of_dvd_unit (Nat.cast_dvd_cast
    (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hann))
  simpa only [Nat.cast_pow] using (hInvert x).pow n

private theorem pullback_fibre_dimension
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) {Z : Scheme.{u}} (y : Z ⟶ Y') :
    topologicalKrullDim ↥(pullback f' y) =
      topologicalKrullDim ↥(pullback f (y ≫ g)) := by
  have hs : IsPullback g' f' f g :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  let e := ((IsPullback.of_hasPullback f' y).paste_horiz hs).isoPullback
  exact (Scheme.homeoOfIso e).isHomeomorph.topologicalKrullDim_eq _

/-- A proper Cartesian square has finite-level amplification with common bound `2 * e`.
Source: blueprint main-20261015, sec-proper-base-change/sk-thm-properbasechange,
thm-weil-pbc-amplification-proper.proof.md, part (a); Stacks Tags 095U and 0GL0
(blueprint: lem-weil-pbc-finite-amplification-proper).

Proof: evaluating the annihilator at one gives N in I. Thus N^n kills A/I^n, and
all additive orders in that quotient divide N^n. Since N is invertible at each stalk,
those orders are invertible there as well. Paste the Cartesian square with each
geometric point of Yprime. Its fibre is isomorphic to the fibre of f at the composite
point over the same algebraically closed field, hence has the same dimension, also
when the fibre is empty. Apply proper direct-image finiteness to both vertical maps
at every positive quotient. Exact inverse image preserves bounded constructibility
and every cohomological interval for both horizontal maps. Identify the predecessor
index used by the finite pullback interval theorem with the given positive quotient
by the canonical cast ring equivalence. These are all four clauses of AMP. -/
theorem finiteLevelAmplification_of_isProper
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    {A : Type (u + 1)} [CommRing A] (d : Scheme.AdicCoefficientDatum A)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    (hDimX : ∃ k : ℕ, topologicalKrullDim X ≤ (k : WithBot ℕ∞))
    (hDimY : ∃ k : ℕ, topologicalKrullDim Y ≤ (k : WithBot ℕ∞))
    (hDimX' : ∃ k : ℕ, topologicalKrullDim X' ≤ (k : WithBot ℕ∞))
    (hDimY' : ∃ k : ℕ, topologicalKrullDim Y' ≤ (k : WithBot ℕ∞))
    [IsProper f] [IsProper f']
    (N : ℕ) (hN : 0 < N) (hAnnihilator : ∀ a : A ⧸ d.ideal, N • a = 0)
    (hInvertX : ∀ x : X, IsUnit (N : X.presheaf.stalk x))
    (hInvertY : ∀ y : Y, IsUnit (N : Y.presheaf.stalk y))
    (hInvertX' : ∀ x : X', IsUnit (N : X'.presheaf.stalk x))
    (hInvertY' : ∀ y : Y', IsUnit (N : Y'.presheaf.stalk y))
    (e : ℕ)
    (hFib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim ↥(pullback f y) ≤ (e : WithBot ℕ∞)) :
    Scheme.HasFiniteLevelAmplification sq d (2 * e) := by
  by_cases hzero : N = 0
  · exact (Nat.ne_of_gt hN hzero).elim
  have : IsNoetherianRing A := d.noetherian
  have hfinite : ∀ n : ℕ+, Finite (A ⧸ d.ideal ^ (n : ℕ)) := fun n ↦
    (congrArg (fun k : ℕ ↦ Finite (A ⧸ d.ideal ^ k))
      (Nat.succ_pred_eq_of_pos n.property)).mp (d.quotientFinite (n : ℕ).pred)
  have hfinite' : ∀ n : ℕ, Finite (A ⧸ d.ideal ^ (n + 1)) := d.quotientFinite
  have hOrders (T : Scheme.{u}) (hi : ∀ x : T, IsUnit (N : T.presheaf.stalk x)) :=
    fun (n : ℕ+) ↦ quotient_order_isUnit d.ideal N hAnnihilator hi (n : ℕ)
  refine ⟨inferInstance, inferInstance, hDimY, hDimY',
    hOrders Y hInvertY, hOrders Y' hInvertY', ?_⟩
  intro n
  let : TopologicalSpace (A ⧸ d.ideal ^ (n : ℕ)) := ⊥
  let : DiscreteTopology (A ⧸ d.ideal ^ (n : ℕ)) := ⟨rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact constructibleDirectImageFiniteness_of_isProper A d.ideal d.finitelyGenerated
      _ _ n hDimX hDimY (hOrders X hInvertX n) (hOrders Y hInvertY n) f e
      (fun y ↦ hFib _ (Y.algClosurePoint y))
  · apply constructibleDirectImageFiniteness_of_isProper A d.ideal d.finitelyGenerated
      _ _ n hDimX' hDimY' (hOrders X' hInvertX' n) (hOrders Y' hInvertY' n) f' e
    intro y
    rw [pullback_fibre_dimension sq]
    exact hFib _ (Y'.algClosurePoint y ≫ g)
  all_goals
    refine ⟨inferInstance, inferInstance, ?_, ?_⟩
    · exact fun K hK ↦ finiteCoefficientDerivedPullback_preserves_boundedConstructible _ _ K hK
    · intro a b hab K hK hKbound
      have hn : n.val.pred + 1 = n.val := Nat.succ_pred_eq_of_pos n.property
      let en : (A ⧸ d.ideal ^ (n : ℕ)) ≃+* A ⧸ d.ideal ^ (n.val.pred + 1) :=
        RingEquiv.cast (congrArg (fun k : ℕ ↦ d.ideal ^ k) hn.symm)
      exact (finiteCoefficientBoundedConstructiblePullback_exact_and_interval A
        d.toCompleteCoefficientDatum n.val.pred _ en _).2 ⟨K, hK⟩ a b hKbound

end AlgebraicGeometry.ProEtale
