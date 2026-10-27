module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Group.Units
import Sheaf.RingTheory.ValuationValueGroupTorsion
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Coarsenings of valuations in a finite algebraic field extension

Source: ILO, Travaux de Gabber, XX 4.4, printed p. 374, valued-field background;
Stacks Project, algebra.tex, Tags 00IB, 00ID and 0AAV; more-algebra.tex, Tag 0ASJ,
first proof paragraph (blueprint: lem-per-algebraic-valuation-coarsening-correspondence).

The restricted valuation ring is Mathlib's `W.comap (algebraMap K L)`.
The additive value group is `Additive (OrderDual W.ValueGroupˣ)`: units remove the
zero class of Mathlib's value group with zero, and the order dual changes the
multiplicative valuation order to the additive valuation order of Stacks 00ID.
The image of `Kˣ` under the displayed map is the subgroup denoted by `Γ_V`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace ValuationSubring

private def fractionLift {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (W : ValuationSubring L) (R : ValuationSubring K) : Subring L where
  carrier := {x | ∃ y ∈ W, ∃ s : K, s ≠ 0 ∧ algebraMap K L s ∈ W ∧
    s⁻¹ ∈ R ∧ x = y / algebraMap K L s}
  zero_mem' := ⟨0, W.zero_mem, 1, one_ne_zero, by simp,
    by simp, by simp⟩
  one_mem' := ⟨1, W.one_mem, 1, one_ne_zero, by simp,
    by simp, by simp⟩
  add_mem' := by
    rintro x z ⟨y, hy, s, hs, hsw, hsr, rfl⟩ ⟨t, ht, q, hq, hqw, hqr, rfl⟩
    refine ⟨y * algebraMap K L q + t * algebraMap K L s,
      W.add_mem _ _ (W.mul_mem _ _ hy hqw) (W.mul_mem _ _ ht hsw),
      s * q, mul_ne_zero hs hq, ?_, ?_, ?_⟩
    · simpa only [map_mul] using W.mul_mem _ _ hsw hqw
    · simpa only [mul_inv_rev] using R.mul_mem _ _ hqr hsr
    · rw [map_mul]
      simpa only [mul_comm] using
        div_add_div y t ((map_ne_zero (algebraMap K L)).mpr hs)
          ((map_ne_zero (algebraMap K L)).mpr hq)
  neg_mem' := by
    rintro x ⟨y, hy, s, hs, hsw, hsr, rfl⟩
    exact ⟨-y, W.neg_mem _ hy, s, hs, hsw, hsr, by rw [neg_div]⟩
  mul_mem' := by
    rintro x z ⟨y, hy, s, hs, hsw, hsr, rfl⟩ ⟨t, ht, q, hq, hqw, hqr, rfl⟩
    refine ⟨y * t, W.mul_mem _ _ hy ht, s * q, mul_ne_zero hs hq, ?_, ?_, ?_⟩
    · simpa only [map_mul] using W.mul_mem _ _ hsw hqw
    · simpa only [mul_inv_rev] using R.mul_mem _ _ hqr hsr
    · rw [map_mul, div_mul_div_comm]

private theorem le_fractionLift {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (W : ValuationSubring L) (R : ValuationSubring K) :
    W.toSubring ≤ fractionLift W R := by
  intro x hx
  exact ⟨x, hx, 1, one_ne_zero, by simp,
    by simp, by simp⟩

private theorem fractionLift_comap {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (W : ValuationSubring L) (R : ValuationSubring K)
    (hR : W.comap (algebraMap K L) ≤ R) :
    (fractionLift W R).comap (algebraMap K L) = R.toSubring := by
  ext x
  constructor
  · rintro ⟨y, hy, s, hs, hsw, hsr, he⟩
    have hxy : algebraMap K L (x * s) = y := by
      rw [map_mul, he, div_mul_cancel₀ _ ((map_ne_zero _).mpr hs)]
    have hxs : x * s ∈ R := hR (by change algebraMap K L (x * s) ∈ W; rwa [hxy])
    simpa [mul_assoc, hs] using R.mul_mem _ _ hxs hsr
  · intro hx
    change x ∈ R at hx
    rcases W.mem_or_inv_mem (algebraMap K L x) with hw | hw
    · exact le_fractionLift W R hw
    · by_cases hz : x = 0
      · subst x; simp
      refine ⟨1, W.one_mem, x⁻¹, inv_ne_zero hz, ?_, ?_, ?_⟩
      · simpa only [map_inv₀] using hw
      · simpa only [inv_inv] using hx
      · simp

private theorem mem_of_pow_mem {F : Type*} [Field F] (U : ValuationSubring F)
    {x : F} {n : ℕ} (hn : 0 < n) (hx : x ^ n ∈ U) : x ∈ U := by
  rw [← U.valuation_le_one_iff, map_pow] at hx
  exact U.mem_of_valuation_le_one x
    ((pow_le_one_iff_of_nonneg zero_le hn.ne').mp hx)

private theorem restriction_reflects_le {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] (W U T : ValuationSubring L)
    (hU : W ≤ U) (hT : W ≤ T)
    (h : U.comap (algebraMap K L) ≤ T.comap (algebraMap K L)) : U ≤ T := by
  intro x hx
  by_cases hz : x = 0
  · subst x; exact T.zero_mem
  obtain ⟨n, hn, a, ha, z, hz, hzw, hzi, he⟩ :=
    WeilConjectures.algebraic_extension_value_group_torsion K L W.toSubring
      (fun t _ ↦ W.mem_or_inv_mem t) x hz
  have hau : algebraMap K L a ∈ U := by
    have hm := U.mul_mem _ _ (U.pow_mem hx n) (hU hzi)
    rw [he, mul_assoc, mul_inv_cancel₀ hz, mul_one] at hm
    exact hm
  have hat : algebraMap K L a ∈ T := h hau
  apply mem_of_pow_mem T hn
  rw [he]
  exact T.mul_mem _ _ hat (hT hzw)

/-- Restriction along a finite algebraic field extension identifies the valuation overrings,
and the quotient of the value group by the restricted value group is torsion.

Source: ILO, Travaux de Gabber, XX 4.4, printed p. 374, valued-field background;
Stacks Project, algebra.tex, Tags 00IB, 00ID and 0AAV; more-algebra.tex, Tag 0ASJ,
first proof paragraph (blueprint: lem-per-algebraic-valuation-coarsening-correspondence).

Proof:
1. The inverse alternative for `W` restricts to `K`, giving the valuation ring
   `V = W.comap (algebraMap K L)`, with fraction field `K`; likewise for every
   overring. A nonzero element of `K` is a unit of `W` exactly when it and its
   inverse belong to `V`. Thus `Kˣ / Vˣ` identifies, with its order, with the
   image of `Kˣ` in the value group of `W` (Stacks 00IB and 00ID).
2. Apply `lem-trf-valuation-value-group-torsion`, namely
   `WeilConjectures.algebraic_extension_value_group_torsion`, to `W.toSubring`.
   Each nonzero `x` satisfies `x^n = a*u` with `n > 0`, `a` nonzero in `K`
   and `u` a unit of `W`. Passing to classes gives `n*w(x) = w(a)`.
   Surjectivity of the quotient valuation gives the first conjunct.
3. For an overring `R` of `V`, let `S(R)` consist of nonzero `s` in `V` whose
   inverse belongs to `R`. Define `B(R)` by the fractions `y/s`, with `y` in `W`
   and `s` in `S(R)`. The set `S(R)` contains one and is multiplicatively closed.
   The fraction sum, product and negative formulas show that `B(R)` is a subring.
   It contains `W`, so inherits the inverse alternative and has fraction field `L`.
4. Its restriction is `R`: if `x = y/s` lies in `K`, then `y = s*x` lies in `V`,
   so `x` lies in `R`. Conversely use `x/1` when `x` lies in `V`; otherwise use
   `1/(x⁻¹)`, since `x⁻¹` lies in `V`. Zero is immediate.
5. Restriction reflects inclusion. If `W ≤ U,T` and the restriction of `U` lies
   in the restriction of `T`, take nonzero `x ∈ U` and write `x^n = a*u` by
   Step 2. Then `a = x^n*u⁻¹` lies in the restriction of `U`, hence in that of
   `T`. Thus `x^n ∈ T`. The inequality `v_T(x)^n ≤ 1`, with `n > 0`, implies
   `v_T(x) ≤ 1`, so `x ∈ T`. Zero belongs to every subring. In particular,
   restriction is injective.
6. Step 4 proves surjectivity. Restriction preserves inclusion directly, and
   Step 5 reflects it; the resulting bijection is the stated order isomorphism.
   The field `L` restricts to `K`; injectivity makes it the only
   overring with that restriction. Therefore every proper overring downstairs
   has a proper lift. No henselian or separability assumption is used. -/
theorem algebraic_coarsening_correspondence
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (W : ValuationSubring L) :
    (∀ δ : Additive (OrderDual W.ValueGroupˣ),
      ∃ n : ℕ, 0 < n ∧ ∃ a : Kˣ,
        n • δ = Additive.ofMul (OrderDual.toDual
          (Units.map W.valuation.toMonoidWithZeroHom.toMonoidHom
            (Units.map (algebraMap K L).toMonoidHom a)))) ∧
    (∃ e : {U : ValuationSubring L // W ≤ U} ≃o
        {R : ValuationSubring K // W.comap (algebraMap K L) ≤ R},
      ∀ U : {U : ValuationSubring L // W ≤ U},
        (e U).1 = U.1.comap (algebraMap K L)) ∧
    (∀ U : ValuationSubring L, W ≤ U →
      (U = ⊤ ↔ U.comap (algebraMap K L) = ⊤)) ∧
    (∀ R : ValuationSubring K, W.comap (algebraMap K L) ≤ R → R ≠ ⊤ →
      ∃ U : ValuationSubring L, W ≤ U ∧ U ≠ ⊤ ∧ U.comap (algebraMap K L) = R) := by
  classical
  have htors : ∀ x : L, x ≠ 0 →
      ∃ n : ℕ, 0 < n ∧ ∃ a : K, a ≠ 0 ∧ ∃ z : L,
        z ≠ 0 ∧ z ∈ W ∧ z⁻¹ ∈ W ∧ x ^ n = algebraMap K L a * z :=
    WeilConjectures.algebraic_extension_value_group_torsion K L W.toSubring
      (fun t _ ↦ W.mem_or_inv_mem t)
  have hgroup : ∀ δ : Additive (OrderDual W.ValueGroupˣ),
      ∃ n : ℕ, 0 < n ∧ ∃ a : Kˣ,
        n • δ = Additive.ofMul (OrderDual.toDual
          (Units.map W.valuation.toMonoidWithZeroHom.toMonoidHom
            (Units.map (algebraMap K L).toMonoidHom a))) := by
    intro δ
    obtain ⟨x, hx⟩ := W.valuation_surjective (δ.toMul.ofDual : W.ValueGroupˣ).val
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      exact Units.ne_zero _ (hx.symm.trans (map_zero _))
    obtain ⟨n, hn, a, ha, z, hz, hzw, hzi, he⟩ := htors x hx0
    refine ⟨n, hn, Units.mk0 a ha, ?_⟩
    apply Additive.toMul.injective
    apply OrderDual.ofDual.injective
    apply Units.ext
    change ((δ.toMul.ofDual : W.ValueGroupˣ).val) ^ n = W.valuation (algebraMap K L a)
    rw [← hx, ← map_pow, he, map_mul]
    have hzval : W.valuation z = 1 := by
      apply le_antisymm
      · exact (W.valuation_le_one_iff z).mpr hzw
      · have hi := (W.valuation_le_one_iff z⁻¹).mpr hzi
        rw [map_inv₀] at hi
        exact (inv_le_one₀ ((W.valuation.pos_iff).mpr hz)).mp hi
    rw [hzval, mul_one]
  let f : {U : ValuationSubring L // W ≤ U} →
      {R : ValuationSubring K // W.comap (algebraMap K L) ≤ R} :=
    fun U ↦ ⟨U.1.comap (algebraMap K L), fun _ hx ↦ U.2 hx⟩
  have hf : ∀ U T, f U ≤ f T ↔ U ≤ T := by
    intro U T
    exact ⟨restriction_reflects_le W U.1 T.1 U.2 T.2,
      fun h _ hx ↦ h hx⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro U T h
      exact le_antisymm ((hf U T).mp h.le) ((hf T U).mp h.ge)
    · intro R
      let U := W.ofLE (fractionLift W R.1) (le_fractionLift W R.1)
      refine ⟨⟨U, le_fractionLift W R.1⟩, ?_⟩
      apply Subtype.ext
      apply ValuationSubring.toSubring_injective
      exact fractionLift_comap W R.1 R.2
  let e : {U : ValuationSubring L // W ≤ U} ≃o
      {R : ValuationSubring K // W.comap (algebraMap K L) ≤ R} :=
    { Equiv.ofBijective f hbij with map_rel_iff' := fun {U T} ↦ hf U T }
  have he : ∀ U, (e U).1 = U.1.comap (algebraMap K L) := fun _ ↦ rfl
  have htop : ∀ U : ValuationSubring L, W ≤ U →
      (U = ⊤ ↔ U.comap (algebraMap K L) = ⊤) := by
    intro U hU
    constructor
    · intro h; subst U; rfl
    · intro h
      have hh : e ⟨U, hU⟩ = e ⟨⊤, W.le_top⟩ := Subtype.ext h
      exact congrArg Subtype.val (e.injective hh)
  refine ⟨hgroup, ⟨e, he⟩, htop, ?_⟩
  intro R hR hproper
  let U := e.symm ⟨R, hR⟩
  have hrest : U.1.comap (algebraMap K L) = R := by
    rw [← he U]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨R, hR⟩)
  exact ⟨U.1, U.2, fun h ↦ hproper (hrest.symm.trans ((htop U.1 U.2).mp h)), hrest⟩

end ValuationSubring
