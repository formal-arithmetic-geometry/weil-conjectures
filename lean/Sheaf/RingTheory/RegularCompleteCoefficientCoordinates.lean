/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-! # Coordinates with a specified coefficient field

Source: Stacks Project, Algebra, Tag 0C0S, clause (2) and its proof
(blueprint: lem-trf-regular-complete-coefficient-coordinates).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace IsLocalRing

/-- Every generating list of length equal to the dimension gives complete local coordinates
with the specified coefficient map. Source: Stacks Project, Algebra, Tag 0C0S (2)
(blueprint: lem-trf-regular-complete-coefficient-coordinates).

The equations on constants and variables characterize the evaluation map uniquely by
`MvPowerSeries.exists_ringHom_of_isAdicComplete`. The ideal-comap equation expresses
that this equivalence and its inverse preserve the adic neighbourhoods of zero; hence
it is an isomorphism of complete local algebras with the given coefficient structure.

Proof, following the five steps of the DAG node:
1. If d = 0, generation by the empty list gives maximalIdeal C = 0. The residue
isomorphism is then exactly c, and the zero-variable power-series ring is k
(def-weil-pbc-multivariate-power-series). Both adic topologies are discrete.
2. Set P = k[[T_1,...,T_d]] and I = (T_1,...,T_d). By
lem-weil-pbc-power-series-field-cohen-regular-complete, P is a complete Noetherian
local domain of dimension d with maximal ideal I. Apply
lem-weil-pbc-power-series-universal-property-complete to c and t in maximalIdeal C.
The truncation formula constructs evaluation and sends I^r into (maximalIdeal C)^r.
3. Generation gives I.map evaluation = maximalIdeal C, and the residue hypothesis
makes evaluation surjective modulo that ideal. Source completeness and target
Hausdorffness (def-weil-pbc-adically-complete-ring) allow
lem-weil-pbc-complete-source-surjective-mod-ideal to prove surjectivity.
4. A nonzero kernel element has zero constant coefficient, by the injectivity of the
residue coefficient map, so lies in I. It is a nonzerodivisor because P is a domain.
By lem-weil-pbc-dimension-quotient-nonzerodivisor, its quotient has dimension d - 1.
Surjectivity to C pulls prime chains back injectively, contradicting dim C = d.
Thus evaluation is bijective.
5. Its inverse respects coefficients. Surjectivity and the variable images identify
the images of I^r with (maximalIdeal C)^r for all r. Injectivity gives the displayed
comap equality, proving continuity in both directions and preservation of maximal ideals.
-/
theorem exists_ringEquiv_regular_complete_coefficients
    (k : Type u) [Field k] (C : Type v) [CommRing C]
    [IsRegularLocalRing C] [IsAdicComplete (maximalIdeal C) C]
    (d : ℕ) (hdim : ringKrullDim C = (d : WithBot ℕ∞))
    (c : k →+* C) (hres : Function.Bijective ((residue C).comp c))
    (t : Fin d → C) (ht : ∀ i : Fin d, t i ∈ maximalIdeal C)
    (hgen : Ideal.span (Set.range t) = maximalIdeal C) :
    (∃ e : MvPowerSeries (Fin d) k ≃+* C,
      (∀ a : k, e (MvPowerSeries.C a) = c a) ∧
      (∀ i : Fin d, e (MvPowerSeries.X i) = t i) ∧
      (∀ r : ℕ, Ideal.comap e.toRingHom (maximalIdeal C ^ r) =
        Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) k)) ^ r)) ∧
    (d = 0 → Function.Bijective c) := by
  classical
  let P := MvPowerSeries (Fin d) k
  obtain ⟨f, hfC, hfX, _⟩ :=
    MvPowerSeries.exists_ringHom_of_isAdicComplete (maximalIdeal C) c d t ht
  rcases MvPowerSeries.power_series_field_cohen_regular_complete d
      (Or.inl (Field.toIsField k)) with
      ⟨_, hnoeth, hdomain, hlocal, hvars, _, _, hcomplete, _, hdimP⟩ | ⟨p, hp, _⟩
  · let : IsNoetherianRing P := hnoeth
    let : IsDomain P := hdomain
    let : IsLocalRing P := hlocal
    let : IsAdicComplete (maximalIdeal P) P := hcomplete
    have hmap : Ideal.map f (maximalIdeal P) = maximalIdeal C := by
      rw [hvars, Ideal.map_span]
      have himage : f '' Set.range (MvPowerSeries.X : Fin d → P) = Set.range t := by
        ext y
        constructor
        · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, (hfX i).symm⟩
        · rintro ⟨i, rfl⟩
          exact ⟨MvPowerSeries.X i, ⟨i, rfl⟩, hfX i⟩
      rw [himage, hgen]
    have : IsHausdorff (Ideal.map f (maximalIdeal P)) C := by
      rw [hmap]
      infer_instance
    have hsurj : Function.Surjective f := by
      apply surjective_of_mk_map_comp_surjective (I := maximalIdeal P) f
      rw [hmap]
      intro y
      obtain ⟨a, ha⟩ := hres.surjective y
      refine ⟨MvPowerSeries.C a, ?_⟩
      change Ideal.Quotient.mk (maximalIdeal C) (f (MvPowerSeries.C a)) = y
      rw [hfC]
      exact ha
    have hinj : Function.Injective f := by
      rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
      intro x hx
      by_contra hne
      have hle := ringKrullDim_succ_le_of_surjective f hsurj
        (mem_nonZeroDivisors_iff_ne_zero.mpr hne) hx
      rw [hdim, hdimP] at hle
      have hnat : d + 1 ≤ d := by exact_mod_cast hle
      omega
    let e := RingEquiv.ofBijective f ⟨hinj, hsurj⟩
    refine ⟨⟨e, hfC, hfX, ?_⟩, ?_⟩
    · intro r
      have hpows : Ideal.map f (maximalIdeal P ^ r) = maximalIdeal C ^ r := by
        rw [Ideal.map_pow, hmap]
      rw [← hvars, ← hpows]
      exact Ideal.comap_map_of_bijective f ⟨hinj, hsurj⟩
    · intro hd
      subst d
      refine ⟨c.injective, ?_⟩
      intro y
      obtain ⟨F, hF⟩ := hsurj y
      refine ⟨MvPowerSeries.constantCoeff F, ?_⟩
      rw [← hfC]
      have hconst : MvPowerSeries.C (MvPowerSeries.constantCoeff F) = F :=
        (MvPowerSeries.isEmptyEquiv (Fin 0) k).symm_apply_apply F
      rw [hconst]
      exact hF
  · obtain ⟨_, hdomain, hdvr, _⟩ := hp
    let := hdomain
    let := hdvr
    exact False.elim (IsDiscreteValuationRing.not_isField k (Field.toIsField k))

end IsLocalRing
