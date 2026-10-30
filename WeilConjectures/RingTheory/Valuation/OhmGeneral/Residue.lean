/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.OhmGeneral
public import WeilConjectures.RingTheory.Valuation.GaussResidue
public import WeilConjectures.FieldTheory.AdjoinSimplePow

/-!
# Residues in Ohm's stability setting

In the setting of `ValuationSubring.not_immediate_of_inertiaField` (`K ⊆ Ω` algebraically closed,
`x ∈ 𝒪` with residue `x̄` transcendental over `k`, the residues of `K ∩ 𝒪`, `F = K(x)`):

- `ValuationSubring.residue_mem_adjoin_of_mem_closure`: residues of `F ∩ 𝒪` lie in `k(x̄)`.
- `ValuationSubring.residue_pow_ne_of_isSeparable`: if the residues of a subfield `L ∩ 𝒪` are
  separable over `k(x̄)`, then `x̄` is not a `p`-th power of such a residue.
-/

@[expose] public section

open IsLocalRing IntermediateField

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] {𝒪 : ValuationSubring Ω}

/-- **(R1)** The residues of the integral elements of `K(x)` lie in `k(x̄)`, where `k` is the
residue field of `K` and `x̄` is transcendental over `k`. -/
theorem residue_mem_adjoin_of_mem_closure (K : Subfield Ω) {x : 𝒪}
    (htr : Transcendental (𝒪.residueSubfield K) (residue 𝒪 x)) {y : 𝒪}
    (hy : (y : Ω) ∈ Subfield.closure ((K : Set Ω) ∪ {(x : Ω)})) :
    residue 𝒪 y ∈ adjoin (𝒪.residueSubfield K) {residue 𝒪 x} := by
  refine residue_mem_adjoin_of_mem_adjoin le_rfl htr (F := K) ?_
  rw [← mem_toSubfield, adjoin_toSubfield]
  convert hy using 3
  exact Subtype.range_coe

/-- **(R1)**, subfield form: the residue field of `K(x)` is contained in `k(x̄)`. -/
theorem residueSubfield_closure_le (K : Subfield Ω) {x : 𝒪}
    (htr : Transcendental (𝒪.residueSubfield K) (residue 𝒪 x)) :
    𝒪.residueSubfield (Subfield.closure ((K : Set Ω) ∪ {(x : Ω)})) ≤
      (adjoin (𝒪.residueSubfield K) {residue 𝒪 x}).toSubfield := by
  rintro _ ⟨y, hy, rfl⟩
  exact residue_mem_adjoin_of_mem_closure K htr hy

/-- **(R3)** If the residues of the integral elements of a subfield `L` are separable over
`k(x̄)`, with `x̄` transcendental over `k`, then `x̄` is not the `p`-th power of such a residue. -/
theorem residue_pow_ne_of_isSeparable {p : ℕ} [hp : Fact p.Prime] [CharP (ResidueField 𝒪) p]
    {k : Subfield (ResidueField 𝒪)} {x : 𝒪} (htr : Transcendental k (residue 𝒪 x))
    {L : Subfield Ω}
    (hsep : ∀ w : 𝒪, (w : Ω) ∈ L → IsSeparable (adjoin k {residue 𝒪 x}) (residue 𝒪 w))
    {w : 𝒪} (hw : (w : Ω) ∈ L) : residue 𝒪 w ^ p ≠ residue 𝒪 x := by
  intro hwx
  have : CharP (adjoin k {residue 𝒪 x}) p :=
    (algebraMap (adjoin k {residue 𝒪 x}) (ResidueField 𝒪)).charP
      (algebraMap (adjoin k {residue 𝒪 x}) (ResidueField 𝒪)).injective p
  obtain ⟨c, hc⟩ := mem_bot.1 ((hsep w hw).mem_bot_of_pow_mem (q := p)
    (mem_bot.2 ⟨⟨residue 𝒪 x, mem_adjoin_simple_self k _⟩, hwx.symm⟩))
  exact pow_ne_of_mem_adjoin_simple hp.out.one_lt htr (hc ▸ c.2) hwx
/-- Separability over a subfield `A` of `R` passes to any intermediate field `B ⊇ A`. -/
lemma isSeparable_of_le_toSubfield {R k : Type*} [Field R] [Field k] [Algebra k R]
    {A : Subfield R} {B : IntermediateField k R} (h : A ≤ B.toSubfield) {ζ : R}
    (hs : IsSeparable A ζ) : IsSeparable B ζ := by
  refine Polynomial.Separable.of_dvd (Polynomial.Separable.map (f := Subfield.inclusion h) hs)
    (minpoly.dvd B ζ ?_)
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  exact minpoly.aeval A ζ

/-- **(R2), general form.** Let `Ω` be separably closed and separable algebraic over a subfield
`F`. The residue of every integral element of the inertia field of `𝒪` over `F` is separable
over the residue field of `F`. (The residue field of the inertia field is the separable closure of
the residue field of `F` in that of `Ω`.)

The separability hypothesis is necessary: if `Ω` contained a `p`-th root `y` of an element
`x ∈ F ∩ 𝒪` with transcendental residue, then `y` would lie in every fixed field, and `ȳ` would be
an inseparable residue. -/
theorem isSeparable_residue_of_mem_inertiaField [IsSepClosed Ω] (F : Subfield Ω)
    [Algebra.IsSeparable F Ω] {z : 𝒪} (hz : (z : Ω) ∈ 𝒪.inertiaField F) :
    IsSeparable (𝒪.residueSubfield F) (residue 𝒪 z) := by
  sorry

/-- **(R2)** In Ohm's setting, the residues of the integral elements of the inertia field of
`K(x)` are separable over `k(x̄)`. -/
theorem isSeparable_adjoin_residue_of_mem_inertiaField [IsSepClosed Ω] (K : Subfield Ω) {x : 𝒪}
    (htr : Transcendental (𝒪.residueSubfield K) (residue 𝒪 x))
    [Algebra.IsSeparable (Subfield.closure ((K : Set Ω) ∪ {(x : Ω)})) Ω] {z : 𝒪}
    (hz : (z : Ω) ∈ 𝒪.inertiaField (Subfield.closure ((K : Set Ω) ∪ {(x : Ω)}))) :
    IsSeparable (adjoin (𝒪.residueSubfield K) {residue 𝒪 x}) (residue 𝒪 z) :=
  isSeparable_of_le_toSubfield (residueSubfield_closure_le K htr)
    (isSeparable_residue_of_mem_inertiaField _ hz)

/-- **(R3)** In Ohm's setting, `x̄` is not a `p`-th power in the residue field of the inertia field
of `K(x)`. -/
theorem residue_pow_ne_of_mem_inertiaField [IsSepClosed Ω] {p : ℕ} [Fact p.Prime]
    [CharP (ResidueField 𝒪) p] (K : Subfield Ω) {x : 𝒪}
    (htr : Transcendental (𝒪.residueSubfield K) (residue 𝒪 x))
    [Algebra.IsSeparable (Subfield.closure ((K : Set Ω) ∪ {(x : Ω)})) Ω] {w : 𝒪}
    (hw : (w : Ω) ∈ 𝒪.inertiaField (Subfield.closure ((K : Set Ω) ∪ {(x : Ω)}))) :
    residue 𝒪 w ^ p ≠ residue 𝒪 x :=
  residue_pow_ne_of_isSeparable htr
    (L := (𝒪.inertiaField (Subfield.closure ((K : Set Ω) ∪ {(x : Ω)}))).toSubfield)
    (fun _ hz ↦ isSeparable_adjoin_residue_of_mem_inertiaField K htr hz) hw

end ValuationSubring
