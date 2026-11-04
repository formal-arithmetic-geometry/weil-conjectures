/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Coordinates over a specified coefficient field

Source: Stacks Project, Algebra, Tag 0C0S(2) and its proof
(blueprint: lem-trf-regular-complete-coefficient-coordinates).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace IsLocalRing

/-- A complete regular local ring has power-series coordinates over any specified coefficient
field, using any dimension-sized generating list of its maximal ideal. The coefficient equation
expresses compatibility with the given `k`-algebra structure without choosing another structure
on `C`. The comap equality for every ideal power expresses continuity in both directions for
the variable-adic and maximal-ideal-adic topologies. The empty-list case explicitly asserts
that the given coefficient map itself is an isomorphism.

Source: Stacks Project, Algebra, Tag 0C0S(2) and its proof
(blueprint: lem-trf-regular-complete-coefficient-coordinates).

Proof:
1. Put `P = k[[T_1, ..., T_d]]`. The field case of
   lem-weil-pbc-power-series-field-cohen-regular-complete gives a local domain of dimension
   `d`, complete for its variables ideal `I`, which is its maximal ideal. The universal property
   lem-weil-pbc-power-series-universal-property-complete evaluates coefficients by `c` and
   variables by `t`, giving a ring map `f : P →+* C`, also when `d = 0`.
2. Since `t` generates the maximal ideal, `I.map f = maximalIdeal C`. The residue-field
   hypothesis makes the composite to `C / maximalIdeal C` surjective, already on constants.
   The source is `I`-adically precomplete and the target is `I.map f`-adically Hausdorff.
   Apply lem-weil-pbc-complete-source-surjective-mod-ideal to see that `f` is surjective.
3. A nonzero kernel element is a nonzerodivisor because `P` is a domain. The lemma
   lem-trf-surjective-kernel-nonzerodivisor-dimension-drop would then give
   `dim C + 1 ≤ dim P`, contradicting that both dimensions are the finite integer `d`.
   Thus `f` is injective.
4. Form the ring equivalence from the bijective map `f`. Its coefficient and variable
   equations are those of `f`. Mapping ideal powers gives `map f (I^r) = (maximalIdeal C)^r`.
   Bijectivity then gives the asserted comap equality for every `r`, including zero.
5. When `d = 0`, MvPowerSeries.isEmptyEquiv identifies every series with its constant series.
   Surjectivity of `f` gives surjectivity of `c`; a unital map from a field to the nontrivial
   ring `C` is injective. Therefore `c` is bijective.
-/
theorem exists_ringEquiv_regular_complete_coefficients
    (k : Type u) [Field k] (C : Type v) [CommRing C] [IsRegularLocalRing C]
    [IsAdicComplete (maximalIdeal C) C]
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
  have hfield := MvPowerSeries.power_series_field_cohen_regular_complete
    (Λ := k) d (Or.inl (Field.toIsField k))
  rcases hfield with ⟨_, hnoeth, hdomain, hlocal, hmax, e₀, he₀, hcomplete, _, hdimP⟩ |
    ⟨p, hp, _⟩
  swap
  · obtain ⟨_, _, hdvr, _⟩ := hp
    let := hdvr
    exact (IsDiscreteValuationRing.not_isField k (Field.toIsField k)).elim
  let := hnoeth
  let := hdomain
  let := hlocal
  let := hcomplete
  obtain ⟨f, hfC, hfX, _, _⟩ :=
    MvPowerSeries.exists_ringHom_of_isAdicComplete (maximalIdeal C) c d t ht
  have hmap : (maximalIdeal (MvPowerSeries (Fin d) k)).map f = maximalIdeal C := by
    rw [hmax, Ideal.map_span, ← Set.range_comp]
    simpa only [Function.comp_def, hfX] using hgen
  have hsurj : Function.Surjective f := by
    have : IsHausdorff ((maximalIdeal (MvPowerSeries (Fin d) k)).map f) C := by
      rw [hmap]
      infer_instance
    apply surjective_of_mk_map_comp_surjective f
      (I := maximalIdeal (MvPowerSeries (Fin d) k))
    rw [hmap]
    intro y
    obtain ⟨a, ha⟩ := hres.2 y
    refine ⟨MvPowerSeries.C a, ?_⟩
    simpa only [RingHom.comp_apply, hfC, residue, ResidueField] using ha
  have hinj : Function.Injective f := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro x hx
    by_contra hx0
    have hbad := ringKrullDim_succ_le_of_surjective f hsurj
      (mem_nonZeroDivisors_iff_ne_zero.mpr hx0) hx
    rw [hdim, hdimP] at hbad
    have : d + 1 ≤ d := by exact_mod_cast hbad
    omega
  let e := RingEquiv.ofBijective f ⟨hinj, hsurj⟩
  constructor
  · refine ⟨e, hfC, hfX, ?_⟩
    intro r
    change Ideal.comap f (maximalIdeal C ^ r) = _
    rw [← hmap, ← Ideal.map_pow, Ideal.comap_map_of_bijective f ⟨hinj, hsurj⟩, hmax]
  · intro hd
    subst d
    refine ⟨c.injective, ?_⟩
    intro y
    obtain ⟨F, hF⟩ := hsurj y
    refine ⟨MvPowerSeries.constantCoeff F, ?_⟩
    rw [← hfC]
    change f ((MvPowerSeries.isEmptyEquiv (Fin 0) k).symm
      ((MvPowerSeries.isEmptyEquiv (Fin 0) k) F)) = y
    rw [AlgEquiv.symm_apply_apply]
    exact hF

end IsLocalRing
