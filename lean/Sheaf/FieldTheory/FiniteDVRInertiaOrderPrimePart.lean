/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q111
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Notation
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Sheaf.FieldTheory.FiniteDVRResidueNormalAction
import Sheaf.NumberTheory.DvrGaloisDegreeData

/-!
# Prime-to-residue-characteristic part of finite inertia order

Source: Stacks Project, `literature/stacks-project/more-algebra.tex`,
Tag 09EE (lemma-galois-inertia), first proof paragraph
(blueprint: lem-exc-dvr-inertia-order-prime-part).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped Pointwise

namespace IsDiscreteValuationRing

/-- For a finite normal separable extension of fraction fields of a DVR, the inertia
subgroup at a maximal ideal has order whose prime-to-residue-characteristic part is the
prime-to-residue-characteristic part of the ramification index. The residue extension is
allowed to be inseparable.

Source: Stacks Project, `literature/stacks-project/more-algebra.tex`, Tag 09EE
(lemma-galois-inertia), first proof paragraph (blueprint: lem-exc-dvr-inertia-order-prime-part).

Proof (following the five steps in the node). (1) Write `G = Aut_K(L)`. By
`lem-weil-pbc-finite-galois-fixed-field`, `G` is finite and `Nat.card G = [L : K]`.
By `lem-exc-dvr-galois-degree-data`, the finite set of maximal ideals of the
integral closure has cardinality `g > 0`, the residue degree at `𝔫` is `f > 0`,
the common ramification index is the exponent `e` in `hπ`, and
`Nat.card G = g * e * f`; `G` acts transitively on those ideals. (2) The map
from `G` to that set sending `σ` to `σ(𝔫)` is onto. Its fibres are left cosets
of `D = MulAction.stabilizer G 𝔫`, so orbit-stabilizer gives
`Nat.card D = e * f`. (3) Put `E = B / 𝔫`. By
`lem-exc-dvr-residue-normal-action`, `E` is normal over the residue field and
the residue-action map `D → Aut(E/k)` is onto; its kernel is exactly the inertia
subgroup in the conclusion. (4) The residue extension has characteristic `p`
and degree `f`. By `lem-exc-normal-field-degree-factors`, the order `h` of its
automorphism group satisfies `f = h * p^c` for some `c ≥ 0`. (5) Counting the
fibres of the residue-action map gives `Nat.card I = e * p^c`. Factoring the
positive integer `e` as `p^a * m` with `p ∤ m`, the maximal divisor of `e`
coprime to `p` is `m`; hence the supplied `n` equals `m` and
`Nat.card I = n * p^(a+c)`. This proves the stated existential, while the
finite-group input in (1) proves `Finite I`.
-/
theorem inertia_order_prime_part
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (𝔫 : Ideal (integralClosure A L)) [𝔫.IsMaximal]
    [hC : IsDiscreteValuationRing (Localization.AtPrime 𝔫)]
    [hlocal : IsLocalHom (algebraMap A (Localization.AtPrime 𝔫))]
    (πA : A) (hπA : IsLocalRing.maximalIdeal A = Ideal.span {πA})
    (t : Localization.AtPrime 𝔫)
      (ht : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫) = Ideal.span {t})
    (e : ℕ) (he : 0 < e)
    (u : (Localization.AtPrime 𝔫)ˣ)
    (hπ : algebraMap A (Localization.AtPrime 𝔫) πA = (u : Localization.AtPrime 𝔫) * t ^ e)
    (n : ℕ) (hn_dvd : n ∣ e) (hn_coprime : Nat.Coprime n p)
    (hn_max : ∀ d : ℕ, d ∣ e → Nat.Coprime d p → d ≤ n) :
    Finite (𝔫.inertia (MulAction.stabilizer Gal(L / K) 𝔫)) ∧
      ∃ b : ℕ, Nat.card (𝔫.inertia (MulAction.stabilizer Gal(L / K) 𝔫)) = n * p ^ b := by
  classical
  have : IsLocalHom (algebraMap A (Localization.AtPrime 𝔫)) := hlocal
  let B := integralClosure A L
  let k := A ⧸ IsLocalRing.maximalIdeal A
  let E := B ⧸ 𝔫
  let : Field k := residueNormalBaseField A
  let : Field E := residueNormalQuotientField A L 𝔫
  have : Module.Free k E := Module.Free.of_divisionRing k E
  let G := Gal(L / K)
  let X := (IsLocalRing.maximalIdeal A).primesOver B
  obtain ⟨hXfin, hXne, hmax, htrans, hlocalizations, hindices, e₀, f, g,
    he₀, hf, hg, hconstant, hdegree⟩ :=
    NumberTheory.dvr_galois_degree_data A K L B
  have hnX : 𝔫 ∈ X := (hmax 𝔫).mp inferInstance
  have ht' := (irreducible_iff_uniformizer t).mpr ht
  obtain ⟨e₁, f₁, he₁, hf₁, u₁, hπ₁, heq₁, hfq₁⟩ :=
    hindices πA ((irreducible_iff_uniformizer πA).mpr hπA) ⟨𝔫, hnX⟩ t ht'
  have he₁eq : e₁ = e := by
    have hv := (addVal_def _ u₁ ht' e₁ hπ₁).symm.trans (addVal_def _ u ht' e hπ)
    exact_mod_cast hv
  have he₀eq : e₀ = e := (hconstant ⟨𝔫, hnX⟩).1.symm.trans (heq₁.symm.trans he₁eq)
  subst e₀
  have hfq : 𝔫.inertiaDeg A = Module.finrank k E :=
    Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal A) 𝔫
  have hfrank : Module.finrank k E = f := hfq.symm.trans (hconstant ⟨𝔫, hnX⟩).2
  have hEfin : FiniteDimensional k E :=
    Module.finite_of_finrank_pos (hfrank.symm ▸ hf)
  have := htrans
  have hact (σ : G) (q : X) : (σ • q).val = σ • q.val := by
    rw [Ideal.coe_smul_primesOver_eq_map_galRestrict K L]
    have hr : (galRestrict A K L B σ).toRingHom =
        MulSemiringAction.toRingHom G B σ := by
      apply RingHom.ext
      intro x
      apply Subtype.ext
      exact algebraMap_galRestrict_apply A σ x
    exact congrArg (fun f : B →+* B ↦ Ideal.map f q.val) hr
  have horbit : MulAction.orbit G 𝔫 = X := by
    ext q
    constructor
    · rintro ⟨σ, rfl⟩
      have hm := (σ • (⟨𝔫, hnX⟩ : X)).property
      rwa [hact] at hm
    · intro hq
      obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq G (⟨𝔫, hnX⟩ : X) ⟨q, hq⟩
      refine ⟨σ, ?_⟩
      change σ • 𝔫 = q
      calc
        σ • 𝔫 = (σ • (⟨𝔫, hnX⟩ : X)).val := (hact σ ⟨𝔫, hnX⟩).symm
        _ = q := congrArg (fun r : X ↦ r.val) hσ
  have hcount : g * Nat.card (MulAction.stabilizer G 𝔫) = Nat.card G := by
    rw [hg]
    change X.ncard * _ = _
    rw [← horbit]
    simpa only [Nat.card_prod, Nat.card_coe_set_eq] using
      Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G 𝔫)
  have hgpos : 0 < g := by
    rw [hg]
    exact (Set.ncard_pos hXfin).mpr hXne
  have hD : Nat.card (MulAction.stabilizer G 𝔫) = e * f := by
    rw [IsGalois.card_aut_eq_finrank K L, hdegree, mul_assoc] at hcount
    exact Nat.eq_of_mul_eq_mul_left hgpos hcount
  obtain ⟨hnormal, hsurj⟩ := residue_normal_action A K L 𝔫
  have := hnormal
  let ρ := residueNormalActionHom A K L 𝔫
  have hker : ρ.ker = 𝔫.inertia (MulAction.stabilizer G 𝔫) :=
    Ideal.Quotient.ker_stabilizerHom 𝔫 (IsLocalRing.maximalIdeal A) G
  have hIk : Nat.card ρ.ker * Nat.card (E ≃ₐ[k] E) = e * f := by
    rw [← hD, ← ρ.ker.card_mul_index, Subgroup.index_ker]
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
  have hsep : Field.finSepDegree k E = Nat.card (E ≃ₐ[k] E) := by
    rw [Field.finSepDegree_eq_of_isAlgClosed k E (AlgebraicClosure E)]
    exact Nat.card_congr (Normal.algHomEquivAut k (AlgebraicClosure E) E)
  have : CharP k p := inferInstanceAs (CharP (IsLocalRing.ResidueField A) p)
  obtain ⟨c, hc⟩ := finInsepDegree_eq_pow (F := k) (E := E) p
  have hfactor : f = Nat.card (E ≃ₐ[k] E) * p ^ c := by
    rw [← hfrank, ← Field.finSepDegree_mul_finInsepDegree k E, hsep, hc]
  have hI : Nat.card (𝔫.inertia (MulAction.stabilizer G 𝔫)) = e * p ^ c := by
    rw [hker, hfactor] at hIk
    have hpos : 0 < Nat.card (E ≃ₐ[k] E) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hIk
  refine ⟨inferInstance, ?_⟩
  have hp : p.Prime := Fact.out
  have hn' : n = ordCompl[p] e := by
    apply Nat.le_antisymm
    · apply Nat.le_of_dvd (Nat.ordCompl_pos p he.ne')
      exact Nat.dvd_ordCompl_of_dvd_not_dvd hn_dvd
        (hp.coprime_iff_not_dvd.mp hn_coprime.symm)
    · exact hn_max _ (Nat.ordCompl_dvd e p) (Nat.coprime_ordCompl hp he.ne').symm
  refine ⟨e.factorization p + c, ?_⟩
  rw [hI, hn', pow_add, ← mul_assoc, mul_comm (ordCompl[p] e),
    Nat.ordProj_mul_ordCompl_eq_self]

end IsDiscreteValuationRing
