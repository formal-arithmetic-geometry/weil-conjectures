/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralReconstructionInterfaces
public import WeilConjectures.SixFunctors.IntegralSystemRealization.ConstructibleReductionGood
public import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
public import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.Integral.IntegralReductionDevissage

/-!
# Integral constructible complexes as towers

Let `E/ℚ_ℓ` be finite with ring of integers `𝒪_E` and uniformizer `π`, and let `T` be a scheme
over an algebraic closure `k` of a finite field of characteristic `p ≠ ℓ`. We compare the bounded
constructible complexes `Dᵇc(T, 𝒪_E)` (`sfIntegralConstructible`) with towers.

A tower is an object of the derived category of the ringed sequence site
(`coefficientSequenceDerived`): a system `(C_n)_n` of sheaves of `𝒪_E/π^{n+1}`-modules with
quotient-linear transition maps. The reduction `red_T M = (M ⊗ᴸ 𝒪_E/π^{n+1})_n` is the reduction
functor of the canonical calculus `pullbackTensorCalculus`, left adjoint to the total derived limit
`R lim = coefficientSequenceLimit`; its unit projects to the reduction maps `M ⟶ M/π^{n+1}`
(`CoefficientDerivedSystemReduction.unit_projection`). This is blueprint
`lemma-sp-tower-adjunction-foundation--1`, see also `coefficientSequenceReductionAdjunction_exists`.
A tower is *constructible and normalized* (`ExceptionalIntegralReconstruction.normalized`) if its
reduction maps `C_n ⊗ᴸ 𝒪_E/π^{m+1} ⟶ C_m` are isomorphisms and all levels are constructible with
cohomology and Tor amplitude in one interval independent of `n`.

The blueprint indexes the reductions by the powers `ℓ^n`; the powers `π^{n+1}` used here contain
them (`ℓ^n 𝒪_E = π^{en} 𝒪_E` for the ramification index `e`), so the statements below cover the
blueprint's reductions `K/ℓ^n`.

## Main statements

* `AlgebraicGeometry.ProEtale.exists_bounds_reduction_of_sfIntegralConstructible`: blueprint
  `proposition-sp-integral-towers--1`, uniform bounds for the reductions of `K ∈ Dᵇc(T, 𝒪_E)`.
* `AlgebraicGeometry.ProEtale.sfIntegralConstructible_of_isSfDerivedComplete`: blueprint
  `proposition-sp-integral-towers--2`, a derived complete complex with a constructible reduction
  of finite Tor amplitude is in `Dᵇc(T, 𝒪_E)`.
* `AlgebraicGeometry.ProEtale.reductionAdjunction_restrict_sfIntegralConstructible`: blueprint
  `lemma-sp-tower-adjunction-foundation--2`, the adjunction `red_T ⊣ R lim` restricts to an
  equivalence between `Dᵇc(T, 𝒪_E)` and the normalized constructible towers.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.ExceptionalIntegralReconstruction

open IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Derived completeness of an integral complex in the sense of `IsSfDerivedComplete` agrees with
completeness on the full slice site. -/
theorem isSfDerivedComplete_iff_isComplete (T : Scheme.{u}) (K : Integral l E T) :
    IsSfDerivedComplete l E T K ↔ IntegralOnSlice.IsComplete l E T none K := by
  constructor
  · intro hK
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    let : Fact p.Prime := ⟨hprime⟩
    let F : FiniteFieldDatum.{0} :=
      { p := p, a := 1, q := p, prime := hprime, exponent_pos := le_rfl,
        cardinality_eq := (pow_one p).symm, k₀ := ZMod p,
        card_base := by simp [Nat.card_eq_fintype_card], k := AlgebraicClosure (ZMod p) }
    have hl : l ≠ F.p := by change l ≠ p; omega
    exact ⟨F, hl, (sfDerivedComplete_iff_legacy l E T F hl K).mp hK⟩
  · rintro ⟨F, hl, hK⟩
    exact (sfDerivedComplete_iff_legacy l E T F hl K).mpr hK

/-- Constructibility, a cohomological interval and a Tor interval at a finite level are invariant
under isomorphism. -/
theorem finiteLevelBounds_of_iso (T : Scheme.{u}) (n : ℕ)
    {K L : proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E (n + 1))}
    (e : K ≅ L) {a b c d : ℤ}
    (hK : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) T K ∧
      proEtaleCohomologicalSupport K ⊆ Set.Icc a b ∧
      HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E (n + 1)) K c d) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) T L ∧
      proEtaleCohomologicalSupport L ⊆ Set.Icc a b ∧
      HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E (n + 1)) L c d := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) T) :=
    (proEtale_bounded_constructible_isTriangulated T A).1
  refine ⟨ObjectProperty.prop_of_iso _ e hK.1, ?_, hK.2.2.1, ?_⟩
  · intro i hi
    apply hK.2.1
    intro hz
    exact hi (((DerivedCategory.homologyFunctor _ i).mapIso e).isZero_iff.mp hz)
  · intro N P hN f hf hP M i hi
    obtain ⟨q⟩ := hN
    exact hK.2.2.2 N P ⟨q ≪≫ e.symm⟩ f hf hP M i hi

/-- An integral complex is bounded constructible with uniformly bounded finite Tor amplitude if
and only if it is derived complete and its reduction tower has uniform level bounds. -/
theorem finiteTorConstructibleIntegral_iff (T : Scheme.{u}) (K : Integral l E T) :
    finiteTorConstructibleIntegral l E T K ↔
      IsSfDerivedComplete l E T K ∧
        LevelBounds l E T ((calculus l E T).reduction.obj K) := by
  constructor
  · rintro ⟨⟨hc, a, b, hab, h⟩, c, d, hcd, ht⟩
    refine ⟨hc, a, b, c, d, hab, hcd, fun n ↦ ?_⟩
    exact finiteLevelBounds_of_iso l E T n (((calculus l E T).reductionEvaluation n).symm.app K)
      ⟨(h n).1, (h n).2, ht n⟩
  · rintro ⟨hc, a, b, c, d, hab, hcd, h⟩
    have h' := fun n ↦ finiteLevelBounds_of_iso l E T n
      (((calculus l E T).reductionEvaluation n).app K) (h n)
    exact ⟨⟨hc, a, b, hab, fun n ↦ ⟨(h' n).1, (h' n).2.1⟩⟩,
      c, d, hcd, fun n ↦ (h' n).2.2⟩

end WeilConjectures.ExceptionalIntegralReconstruction

namespace AlgebraicGeometry.ProEtale

open WeilConjectures WeilConjectures.IntegralSystemRealization
  WeilConjectures.ExceptionalIntegralReconstruction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Widening the interval preserves Tor amplitude. -/
private lemma hasProEtaleTorAmplitude_mono {T : Scheme.{u}} {A : Type u} [CommRing A]
    {K : proEtaleDerivedCategory T A} {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b')
    (h : HasProEtaleTorAmplitude T A K a b) : HasProEtaleTorAmplitude T A K a' b' :=
  ⟨by have := h.1; omega, fun L P hL f hf hP M i hi ↦
    h.2 L P hL f hf hP M i (by omega)⟩

/-- Blueprint `proposition-sp-integral-towers--1`: **uniform bounds for the reductions of an
integral constructible complex**. Let `T` be a scheme over an algebraic closure of a finite field
of characteristic `p ≠ ℓ`. For `K ∈ Dᵇc(T, 𝒪_E)` there are integers `a ≤ b` such that every
reduction `K/π^{n+1} = K ⊗ᴸ 𝒪_E/π^{n+1}` lies in `Dᵇctf(T_proét, 𝒪_E/π^{n+1})`, with cohomology
and Tor amplitude in `[a, b]`. The reductions `K/ℓ^n` of the blueprint are among these. -/
theorem exists_bounds_reduction_of_sfIntegralConstructible (D : FiniteFieldDatum.{u})
    (hl : l ≠ D.p) (T : Scheme.{u}) [T.Over (Spec (.of D.k))] (K : Integral l E T)
    (hK : sfIntegralConstructible l E T K) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ,
      intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) T
          ((scalarReductionDerivedExtension l E T n).obj K) ∧
        proEtaleCohomologicalSupport ((scalarReductionDerivedExtension l E T n).obj K) ⊆
          Set.Icc a b ∧
        HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension l E T n).obj K) a b := by
  obtain ⟨-, hB, -⟩ :=
    constructibleReduction_good l E D hl (Over.mk (T ↘ Spec (.of D.k))) K hK
  obtain ⟨⟨-, a, b, hab, h⟩, c, d, -, ht⟩ := (finiteTorConstructibleIntegral_iff l E T K).mpr
    ⟨hK.1, hB⟩
  exact ⟨min a c, max b d, (min_le_left a c).trans (hab.trans (le_max_left b d)), fun n ↦
    ⟨(h n).1, (h n).2.trans (Set.Icc_subset_Icc (min_le_left a c) (le_max_left b d)),
      hasProEtaleTorAmplitude_mono (min_le_right a c) (le_max_right b d) (ht n)⟩⟩

/-- On a scheme over an algebraic closure of a finite field of characteristic `p ≠ ℓ`, every
bounded constructible integral complex has uniformly bounded finite Tor amplitude: the
constructible complexes are the finite-Tor constructible ones. The second conjunct of
`WeilConjectures.integral_residue_tor` proves the same equality of predicates on schemes whose
residue fields have `ℓ` invertible; here the hypothesis is a structure morphism to `Spec k`
instead, and the proof goes through `constructibleReduction_good`. -/
theorem finiteTorConstructibleIntegral_eq_sfIntegralConstructible
    (D : FiniteFieldDatum.{u})
    (hl : l ≠ D.p) (T : Scheme.{u}) [T.Over (Spec (.of D.k))] :
    finiteTorConstructibleIntegral l E T = sfIntegralConstructible l E T := by
  refine le_antisymm (fun K hK ↦ hK.1) (fun K hK ↦ ⟨hK, ?_⟩)
  obtain ⟨a, b, hab, h⟩ := exists_bounds_reduction_of_sfIntegralConstructible l E D hl T K hK
  exact ⟨a, b, hab, fun n ↦ (h n).2.2⟩

/-- Blueprint `proposition-sp-integral-towers--2`: **a derived complete complex with a
constructible reduction of finite Tor amplitude is constructible**. Let `T` be a scheme. If `K` is
derived complete and some reduction `K/π^{m+1}` lies in `Dᵇctf(T_proét, 𝒪_E/π^{m+1})`, then
`K ∈ Dᵇc(T, 𝒪_E)`. The blueprint's hypothesis on `K/ℓ` is the case `π^{m+1} 𝒪_E = ℓ 𝒪_E`; its
hypotheses that `T` is of finite type over an algebraic closure of a finite field of
characteristic `p ≠ ℓ` are not needed.

Proof: the residue reduction `K/π` is bounded constructible
(`residue_constructible_of_reduction`), hence so is every reduction `K/π^{n+1}`, with cohomology
in one interval (`reduction_constructible_of_residue`). -/
theorem sfIntegralConstructible_of_isSfDerivedComplete (T : Scheme.{u})
    (K : Integral l E T) (hK : IsSfDerivedComplete l E T K) (m : ℕ)
    (hm : intrinsicFiniteTorsionConstructible l E (m + 1) (Nat.succ_pos m) T
      ((scalarReductionDerivedExtension l E T m).obj K))
    (a b : ℤ) (ht : HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E (m + 1))
      ((scalarReductionDerivedExtension l E T m).obj K) a b) :
    sfIntegralConstructible l E T K := by
  obtain ⟨a', b', hab', h₀, hs₀⟩ := residue_constructible_of_reduction l E T K m ⟨hm, a, b, ht⟩
  exact ⟨hK, a', b', hab', reduction_constructible_of_residue l E T K a' b' h₀ hs₀⟩

/-- Blueprint `lemma-sp-tower-adjunction-foundation--2`: **the adjunction `red_T ⊣ R lim`
restricts to an equivalence between `Dᵇc(T, 𝒪_E)` and the normalized constructible towers**. Let
`T` be a scheme over an algebraic closure of a finite field of characteristic `p ≠ ℓ`, and let
`red_T ⊣ R lim` be the reduction adjunction of the canonical calculus (blueprint
`lemma-sp-tower-adjunction-foundation--1`). Then `red_T` maps `Dᵇc(T, 𝒪_E)` to normalized
constructible towers and its unit is an isomorphism there, and `R lim` maps normalized
constructible towers to `Dᵇc(T, 𝒪_E)` and the counit is an isomorphism there. -/
theorem reductionAdjunction_restrict_sfIntegralConstructible (D : FiniteFieldDatum.{u})
    (hl : l ≠ D.p) (T : Scheme.{u}) [T.Over (Spec (.of D.k))] :
    (∀ K : Integral l E T, sfIntegralConstructible l E T K →
      normalized l E T ((calculus l E T).reduction.obj K) ∧
        IsIso ((calculus l E T).adjunction.unit.app K)) ∧
    ∀ N : System l E T, normalized l E T N →
      sfIntegralConstructible l E T ((coefficientSequenceLimit l E T).obj N) ∧
        IsIso ((calculus l E T).adjunction.counit.app N) := by
  have hR := purNormalizedReconstructionOfScheme l E T (calculus l E T)
  refine ⟨fun K hK ↦ ?_, fun N hN ↦ ?_⟩
  · have hK' := (finiteTorConstructibleIntegral_iff l E T K).mp
      ((finiteTorConstructibleIntegral_eq_sfIntegralConstructible l E D hl T).symm ▸ hK)
    exact ⟨⟨(calculus l E T).reduction_normalized K, hK'.2⟩,
      hR.2 K ((isSfDerivedComplete_iff_isComplete l E T K).mp hK.1)⟩
  · obtain ⟨hc, hi⟩ := hR.1 N hN.1
    refine ⟨((finiteTorConstructibleIntegral_iff l E T _).mpr
      ⟨(isSfDerivedComplete_iff_isComplete l E T _).mpr hc, ?_⟩).1, hi⟩
    obtain ⟨a, b, c, d, hab, hcd, h⟩ := hN.2
    refine ⟨a, b, c, d, hab, hcd, fun n ↦ ?_⟩
    exact finiteLevelBounds_of_iso l E T n
      (((coefficientSequenceDerivedEvaluation l E T n).mapIso
        (@asIso _ _ _ _ ((calculus l E T).adjunction.counit.app N) hi)).symm) (h n)

end AlgebraicGeometry.ProEtale
