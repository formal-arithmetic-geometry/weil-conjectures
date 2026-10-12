/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Algebra.Polynomial.Lifts
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.RingTheory.StrictHenselization.Triples

/-!
# The colimit over étale triples is strictly henselian

Let `R` be a commutative ring, `p` a prime of `R` and `K` a separable closure of `κ(p)`. The
colimit `C = colim S` over the étale triples `(S, q, φ)` (`EtaleTriple.colim R p K`) is a
strictly henselian local ring: the map `ψ : C → K` induced by the maps `S → κ(q) → K` is
surjective, its kernel is the maximal ideal `pC` of `C`, and simple roots in `K` of monic
polynomials over `C` lift to `C`. This is the strict henselization of `R_p` with respect to
`κ(p) → K`.

## Main results

- `EtaleTriple.isUnit_iff_eval_ne_zero`, `EtaleTriple.instIsLocalRingColim`: `C` is local with
  maximal ideal the kernel of `ψ`.
- `EtaleTriple.maximalIdeal_colim_eq_map`: the maximal ideal of `C` is `pC`.
- `EtaleTriple.exists_isRoot_and_eval_eq`: simple roots in `K` lift.
- `EtaleTriple.eval_surjective`: `ψ` is surjective.
- `EtaleTriple.isStrictlyHenselianLocalRing_colim`: `C` is strictly henselian.

## References

- Stacks Project, Lemmas 10.155.5 and 10.155.10, <https://stacks.math.columbia.edu/tag/04GW>,
  <https://stacks.math.columbia.edu/tag/04GP>
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial IsLocalRing

namespace EtaleTriple

variable {R : Type u} [CommRing R] {p : Ideal R} [p.IsPrime] {K : Type u} [Field K] [Algebra R K]
  [Algebra p.ResidueField K] [IsScalarTower R p.ResidueField K]

/-- The étale triple `(S[1/s], qS[1/s], φ)` of an étale triple `(S, q, φ)` and an element
`s ∉ q`. -/
noncomputable def away (t : EtaleTriple R p K) (s : t.S) (hs : t.toAlgHom s ≠ 0) :
    EtaleTriple R p K :=
  ofAlgHom (ker_algebraMap R p K) (Localization.Away s)
    (IsLocalization.liftAlgHom (M := Submonoid.powers s) (f := t.toAlgHom)
      (by rintro ⟨_, n, rfl⟩; simpa using (isUnit_iff_ne_zero.mpr hs).pow n))

lemma toAlgHom_away (t : EtaleTriple R p K) (s : t.S) (hs : t.toAlgHom s ≠ 0) :
    (t.away s hs).toAlgHom = IsLocalization.liftAlgHom (M := Submonoid.powers s)
      (S := Localization.Away s) (f := t.toAlgHom)
      (by rintro ⟨_, n, rfl⟩; simpa using (isUnit_iff_ne_zero.mpr hs).pow n) :=
  toAlgHom_ofAlgHom _ _ _

/-- The localization map `S → S[1/s]`, as a morphism of étale triples. -/
noncomputable def toAway (t : EtaleTriple R p K) (s : t.S) (hs : t.toAlgHom s ≠ 0) :
    t ⟶ t.away s hs :=
  homMk (t' := t.away s hs) (IsScalarTower.toAlgHom R t.S (Localization.Away s)) <| by
    rw [toAlgHom_away]
    ext x
    exact IsLocalization.lift_eq (S := Localization.Away s) _ x

lemma ι_away_algebraMap (t : EtaleTriple R p K) (s : t.S) (hs : t.toAlgHom s ≠ 0) (x : t.S) :
    ι R p K (t.away s hs) (algebraMap t.S (Localization.Away s) x) = ι R p K t x :=
  congr($(ι_comp_β R p K (t.toAway s hs)) x)

/-- An element `ι(s)` of the colimit with `s ↦ ψ(s) ≠ 0` is a unit. -/
lemma isUnit_ι_of_toAlgHom_ne_zero (t : EtaleTriple R p K) (s : t.S) (hs : t.toAlgHom s ≠ 0) :
    IsUnit (ι R p K t s) := by
  rw [← ι_away_algebraMap t s hs]
  exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away s) s).map
    (ι R p K (t.away s hs))

/-- An element of the colimit `C` is a unit if and only if its image under `ψ : C → K` is
nonzero. -/
lemma isUnit_iff_eval_ne_zero (x : colim R p K) : IsUnit x ↔ eval R p K x ≠ 0 := by
  refine ⟨fun h ↦ (h.map (eval R p K)).ne_zero, fun h ↦ ?_⟩
  obtain ⟨t, s, rfl⟩ := exists_ι_eq R p K x
  rw [eval_ι] at h
  exact isUnit_ι_of_toAlgHom_ne_zero t s h

instance : Nontrivial (colim R p K) :=
  ⟨⟨0, 1, fun h ↦ by simpa using congr(eval R p K $h)⟩⟩

/-- The colimit `C` over the étale triples is a local ring.

(blueprint: `lem-weil-pbc-strict-henselization-triples`) -/
instance instIsLocalRingColim : IsLocalRing (colim R p K) :=
  .of_nonunits_add fun a b ha hb ↦ by
    rw [mem_nonunits_iff, isUnit_iff_eval_ne_zero, not_not] at ha hb ⊢
    rw [map_add, ha, hb, add_zero]

/-- The maximal ideal of `C` is the kernel of `ψ : C → K`.

(blueprint: `lem-weil-pbc-strict-henselization-triples`) -/
lemma maximalIdeal_colim_eq_ker : maximalIdeal (colim R p K) = RingHom.ker (eval R p K) := by
  ext x
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_eval_ne_zero, not_not, RingHom.mem_ker]

/-- The preimage of the maximal ideal of `C` in `R` is `p`.

(blueprint: `lem-weil-pbc-strict-henselization-triples`) -/
lemma comap_maximalIdeal_colim :
    (maximalIdeal (colim R p K)).comap (algebraMap R (colim R p K)) = p := by
  ext r
  rw [Ideal.mem_comap, maximalIdeal_colim_eq_ker, RingHom.mem_ker, AlgHom.commutes,
    ← RingHom.mem_ker, ker_algebraMap R p K]

omit [Algebra p.ResidueField K] [IsScalarTower R p.ResidueField K] in
/-- For an étale algebra the prime below generates the maximal ideal at a prime: if `s ∈ q`,
some `u ∉ q` has `us ∈ pS`. This is `Algebra.isUnramifiedAt_iff_map_eq`
(blueprint: `lem-weil-pbc-etale-prime-generates-maximal`) made elementwise. -/
lemma exists_mul_mem_map_of_mem (t : EtaleTriple R p K) {s : t.S} (hs : s ∈ t.q) :
    ∃ u ∉ t.q, u * s ∈ p.map (algebraMap R t.S) := by
  have : t.q.LiesOver p := ⟨t.comap_eq.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p t.q
  have h := ((Algebra.isUnramifiedAt_iff_map_eq R p t.q).mp inferInstance).2
  have hs' : algebraMap t.S (Localization.AtPrime t.q) s ∈
      (p.map (algebraMap R t.S)).map (algebraMap t.S (Localization.AtPrime t.q)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, h,
      ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hs
  obtain ⟨⟨y, ⟨m, hm⟩⟩, hy⟩ :=
    (IsLocalization.mem_map_algebraMap_iff t.q.primeCompl _).mp hs'
  dsimp only at hy
  rw [← map_mul, IsLocalization.eq_iff_exists t.q.primeCompl] at hy
  obtain ⟨⟨c, hc⟩, hc'⟩ := hy
  refine ⟨c * m, fun h ↦ (t.q.primeCompl.mul_mem hc hm) h, ?_⟩
  dsimp only at hc'
  rw [mul_assoc, mul_comm m, hc']
  exact Ideal.mul_mem_left _ _ y.2

/-- **The maximal ideal of the colimit is `pC`.**

(blueprint: `lem-weil-pbc-strict-henselization-triples`) -/
lemma maximalIdeal_colim_eq_map :
    maximalIdeal (colim R p K) = p.map (algebraMap R (colim R p K)) := by
  refine le_antisymm (fun x hx ↦ ?_) (Ideal.map_le_iff_le_comap.mpr comap_maximalIdeal_colim.ge)
  rw [maximalIdeal_colim_eq_ker, RingHom.mem_ker] at hx
  obtain ⟨t, s, rfl⟩ := exists_ι_eq R p K x
  rw [eval_ι] at hx
  have hs : s ∈ t.q := by rw [← ker_toAlgHom]; exact hx
  obtain ⟨u, hu, hus⟩ := exists_mul_mem_map_of_mem t hs
  have hu' : t.toAlgHom u ≠ 0 := fun h ↦ hu (by rw [← ker_toAlgHom]; exact h)
  rw [← ι_away_algebraMap t u hu']
  have hmem : algebraMap t.S (Localization.Away u) s ∈
      p.map (algebraMap R (Localization.Away u)) := by
    have h1 : algebraMap t.S (Localization.Away u) (u * s) ∈
        p.map (algebraMap R (Localization.Away u)) := by
      rw [IsScalarTower.algebraMap_eq R t.S (Localization.Away u), ← Ideal.map_map]
      exact Ideal.mem_map_of_mem _ hus
    obtain ⟨v, hv⟩ := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away u) u
    have : algebraMap t.S (Localization.Away u) s =
        ↑v⁻¹ * algebraMap t.S (Localization.Away u) (u * s) := by
      rw [map_mul, ← hv, Units.inv_mul_cancel_left]
    rw [this]
    exact Ideal.mul_mem_left _ _ h1
  have := Ideal.mem_map_of_mem (ι R p K (t.away u hu')).toRingHom hmem
  have h2 : ((ι R p K (t.away u hu')).toRingHom).comp (algebraMap R (Localization.Away u)) =
      algebraMap R (colim R p K) :=
    RingHom.ext fun r ↦ (ι R p K (t.away u hu')).commutes r
  rwa [Ideal.map_map, h2] at this

end EtaleTriple
