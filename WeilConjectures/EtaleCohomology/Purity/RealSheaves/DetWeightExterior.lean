/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeights
public import WeilConjectures.RepresentationTheory.ExteriorPowerFiltration

/-!
# Determinant weights of exterior powers

Let `ρ` be a nonzero lisse Weil sheaf on a smooth geometrically connected curve `C₀ / 𝔽_q`, with
rank-counted list of determinant weights `L` (`AlgebraicGeometry.WeilGroup.rankDetWeightMultiset`:
the determinant weight `γ_a` of every composition factor `A_a` repeated `dim A_a` times). This file
proves that the determinant weights of the constituents of the exterior power `⋀^r ρ` are exactly
the sums of `r` entries of `L` (blueprint `cor-mg-det-weight-exterior`).

The proof is by induction on the rank. For irreducible `ρ` it is the semisimple case
`Representation.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower`. Otherwise `ρ` has a
proper nonzero subrepresentation `A`, and `⋀^r ρ` has a filtration with steps
`⋀^j A ⊗ ⋀^{r - j} (ρ / A)` (`Representation.nonempty_equiv_exteriorPowerFiltration`); the
two-factor tensor rule (`Representation.exists_detWeight_eq_add_of_subquotient_tprod` and its
converse) and the additivity `L(ρ) = L(A) + L(ρ / A)`
(`AlgebraicGeometry.WeilGroup.rankDetWeightMultiset_eq_add`) reduce the claim to `A` and `ρ / A`.
The finite geometric determinant hypotheses of the tensor rule hold by rank-one purity
(`lem-rp-determinant-weights-agree`).

## Main statements

- `AlgebraicGeometry.WeilGroup.detWeight_subquotient_exteriorPower`: the determinant weights of
  the constituents of `⋀^r ρ` (blueprint `cor-mg-det-weight-exterior`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]

namespace WeilGroup

variable {W : WeilGroup p} {l : ℕ} [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  {ρ : Representation (PadicAlgCl l) W.carrier V} (ι : PadicAlgCl l →+* ℂ)

section Exterior

/-- A subrepresentation of a lisse Weil sheaf is lisse. -/
theorem IsLisse.subrepresentation (hρ : W.IsLisse l ρ) (A : Subrepresentation ρ) :
    W.IsLisse l A.toRepresentation :=
  IsLisse.of_continuous_apply fun φ v ↦ by
    obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend φ (p := A.toSubmodule)
    refine (hρ.continuous_apply ψ v).congr fun g ↦ ?_
    rw [← hψ]
    rfl

/-- A quotient of a lisse Weil sheaf is lisse. -/
theorem IsLisse.quotient (hρ : W.IsLisse l ρ) (A : Subrepresentation ρ) :
    W.IsLisse l A.quotient :=
  IsLisse.of_continuous_apply fun φ v ↦ by
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ v
    exact hρ.continuous_apply (φ ∘ₗ A.toSubmodule.mkQ) v

variable [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] [Fact (ringChar K ≠ l)]
  [W.IsEtaleQuotient]

omit [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] [Fact (ringChar K ≠ l)]
  [W.IsEtaleQuotient] in
/-- The rank-counted list of determinant weights of an irreducible `ρ` is `dw_ι(ρ)` repeated
`rank ρ` times. -/
theorem rankDetWeightMultiset_of_isIrreducible (hirr : ρ.IsIrreducible) :
    W.rankDetWeightMultiset l ρ ι =
      Multiset.replicate (Module.finrank (PadicAlgCl l) V) (W.detWeight l ρ ι) := by
  rw [rankDetWeightMultiset_eq_sum ι (Vs := fun _ : Unit ↦ ⊤)
    Subrepresentation.isInternal_const_top
    fun _ ↦ Subrepresentation.topEquiv.isIrreducible_iff.2 hirr, Fintype.sum_unique,
    ← detWeight_of_equiv ι Subrepresentation.topEquiv, ← Subrepresentation.topEquiv.finrank_eq]

/-- The constituents of an exterior power `⋀^r ρ` of an irreducible lisse Weil sheaf `ρ`: their
determinant weights are sums of `r` entries of the rank-counted list of `ρ`, which consists of
`dw_ι(ρ)` repeated `rank ρ` times. This is the semisimple case
`Representation.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower` for one summand. -/
theorem exists_le_rankDetWeightMultiset_of_isIrreducible (hρ : W.IsLisse l ρ)
    (hirr : ρ.IsIrreducible) (r : ℕ) {U S : Subrepresentation (ρ.exteriorPower r)}
    (hQ : (S.subquotient U).IsIrreducible) :
    ∃ T : Multiset ℝ, T ≤ W.rankDetWeightMultiset l ρ ι ∧ Multiset.card T = r ∧
      W.detWeight l (S.subquotient U) ι = T.sum := by
  have := hirr.nontrivial
  let Vs : Unit → Subrepresentation ρ := fun _ ↦ ⊤
  have hVs (a : Unit) : (Vs a).toRepresentation.IsIrreducible :=
    Subrepresentation.topEquiv.isIrreducible_iff.2 hirr
  let e₀ := Subrepresentation.subquotientInfEquiv U S
  obtain ⟨T, hT, hcard, hsum⟩ :=
    Representation.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower
      (weightCharacter ι (Nat.card K)) W.deg W.frobeniusLift ρ r Vs hVs
      (fun a ↦ (hasFiniteGeometricDet_and_detWeight_eq ι (hρ.subrepresentation (Vs a))).1)
      Subrepresentation.isInternal_const_top (Subrepresentation.inf_lt_of_isIrreducible hQ)
      (e₀.isIrreducible_iff.2 hQ)
      (hasFiniteGeometricDet_and_detWeight_eq ι ((hρ.exteriorPower r).subquotient S _)).1
  refine ⟨T, ?_, hcard, ?_⟩
  · rw [rankDetWeightMultiset_eq_sum ι Subrepresentation.isInternal_const_top hVs]
    convert hT using 1
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [detWeight_weightCharacter]
    rfl
  · rw [detWeight_of_equiv ι e₀, ← hsum, detWeight_weightCharacter]
    rfl

/-- The constituents of an exterior power of a nonzero lisse Weil sheaf, by induction on the rank:
see `AlgebraicGeometry.WeilGroup.detWeight_subquotient_exteriorPower`. -/
theorem detWeight_subquotient_exteriorPower_aux (n : ℕ) {V : Type u} [AddCommGroup V]
    [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V] [Nontrivial V]
    {ρ : Representation (PadicAlgCl l) W.carrier V} (hρ : W.IsLisse l ρ)
    (hn : Module.finrank (PadicAlgCl l) V = n) (r : ℕ) :
    (∀ U S : Subrepresentation (ρ.exteriorPower r), (S.subquotient U).IsIrreducible →
      ∃ T : Multiset ℝ, T ≤ W.rankDetWeightMultiset l ρ ι ∧ Multiset.card T = r ∧
        W.detWeight l (S.subquotient U) ι = T.sum) ∧
    ∀ T : Multiset ℝ, T ≤ W.rankDetWeightMultiset l ρ ι → Multiset.card T = r →
      ∃ U S : Subrepresentation (ρ.exteriorPower r), (S.subquotient U).IsIrreducible ∧
        W.detWeight l (S.subquotient U) ι = T.sum := by
  induction n using Nat.strong_induction_on generalizing V r with
  | _ n ih =>
  by_cases hirr : ρ.IsIrreducible
  · -- the irreducible case: all constituents have weight `r dw_ι(ρ)`
    have hfwd := fun U S hQ ↦ exists_le_rankDetWeightMultiset_of_isIrreducible ι hρ hirr r
      (U := U) (S := S) hQ
    refine ⟨hfwd, fun T hT hcard ↦ ?_⟩
    have hrank := rankDetWeightMultiset_of_isIrreducible ι hirr
    have hrep {T' : Multiset ℝ} (hT' : T' ≤ W.rankDetWeightMultiset l ρ ι) :
        T' = Multiset.replicate (Multiset.card T') (W.detWeight l ρ ι) :=
      Multiset.eq_replicate_of_mem fun x hx ↦ by
        rw [hrank] at hT'
        exact Multiset.eq_of_mem_replicate (Multiset.subset_of_le hT' hx)
    have hr : r ≤ Module.finrank (PadicAlgCl l) V := by
      rw [← hcard, ← card_rankDetWeightMultiset (ρ := ρ) ι]
      exact Multiset.card_le_card hT
    have : Nontrivial (⋀[PadicAlgCl l]^r V) := by
      refine (Module.finrank_pos_iff (R := PadicAlgCl l)).1 ?_
      rw [exteriorPower.finrank_eq]
      exact Nat.choose_pos hr
    have : Nontrivial (Subrepresentation (ρ.exteriorPower r)) :=
      ⟨⊥, ⊤, fun e ↦ bot_ne_top (congrArg Subrepresentation.toSubmodule e)⟩
    obtain ⟨B, -, hB⟩ := Subrepresentation.exists_lt_isIrreducible_subquotient
      (ρ := ρ.exteriorPower r) (A := ⊤) top_ne_bot
    obtain ⟨T', hT', hcard', hsum'⟩ := hfwd B ⊤ hB
    refine ⟨B, ⊤, hB, ?_⟩
    rw [hsum', hrep hT', hrep hT, hcard, hcard']
  -- otherwise `ρ` has a proper nonzero subrepresentation `A`
  obtain ⟨A, hA0, hAtop⟩ : ∃ A : Subrepresentation ρ, A ≠ ⊥ ∧ A ≠ ⊤ := by
    by_contra! h
    have : Nontrivial (Subrepresentation ρ) :=
      ⟨⊥, ⊤, fun e ↦ bot_ne_top (congrArg Subrepresentation.toSubmodule e)⟩
    exact hirr ⟨fun A ↦ (eq_or_ne A ⊥).imp_right (h A)⟩
  have hA0' : A.toSubmodule ≠ ⊥ := fun h ↦
    hA0 (Subrepresentation.toSubmodule_injective (h.trans Subrepresentation.toSubmodule_bot.symm))
  have hAtop' : A.toSubmodule ≠ ⊤ := fun h ↦
    hAtop (Subrepresentation.toSubmodule_injective (h.trans Subrepresentation.toSubmodule_top.symm))
  have : Nontrivial A.toSubmodule := Submodule.nontrivial_iff_ne_bot.2 hA0'
  have : Nontrivial (V ⧸ A.toSubmodule) :=
    Submodule.Quotient.nontrivial_iff.2 hAtop'
  have hdimA : Module.finrank (PadicAlgCl l) A.toSubmodule < n :=
    hn ▸ Submodule.finrank_lt hAtop'
  have hdimQ : Module.finrank (PadicAlgCl l) (V ⧸ A.toSubmodule) < n := by
    have h := Submodule.finrank_quotient_add_finrank A.toSubmodule
    have h' := Module.finrank_pos (R := PadicAlgCl l) (M := A.toSubmodule)
    omega
  have hρA := hρ.subrepresentation A
  have hρQ := hρ.quotient A
  have ihA := ih _ hdimA hρA rfl
  have ihQ := ih _ hdimQ hρQ rfl
  have hadd := rankDetWeightMultiset_eq_add ι A
  -- the filtration of `⋀^r ρ` with steps `⋀^j A ⊗ ⋀^{r - j} (ρ / A)`
  let P := Representation.exteriorPowerFiltration A r
  have hPn : P (r + 1) = ⊥ := Representation.exteriorPowerFiltration_eq_bot A (Nat.lt_succ_self r)
  have hP (j : ℕ) (_ : j < r + 1) : P (j + 1) ≤ P j :=
    Representation.exteriorPowerFiltration_antitone A r (Nat.le_succ j)
  have hP0 : P 0 = ⊤ := Representation.exteriorPowerFiltration_zero A r
  have hdetV (j : ℕ) (UV SV : Subrepresentation (A.toRepresentation.exteriorPower j)) :
      (SV.subquotient UV).HasFiniteGeometricDet W.deg :=
    (hasFiniteGeometricDet_and_detWeight_eq ι ((hρA.exteriorPower j).subquotient SV UV)).1
  have hdetE (j : ℕ) (UE SE : Subrepresentation (A.quotient.exteriorPower j)) :
      (SE.subquotient UE).HasFiniteGeometricDet W.deg :=
    (hasFiniteGeometricDet_and_detWeight_eq ι ((hρQ.exteriorPower j).subquotient SE UE)).1
  have hdet {j : ℕ} (hjr : j ≤ r)
      (U S : Subrepresentation ((A.toRepresentation.exteriorPower j).tprod
        (A.quotient.exteriorPower (r - j)))) :
      (S.subquotient U).HasFiniteGeometricDet W.deg := by
    obtain ⟨e⟩ := Representation.nonempty_equiv_exteriorPowerFiltration A hjr
    exact (hasFiniteGeometricDet_and_detWeight_eq ι
      ((IsLisse.of_equiv e.symm ((hρ.exteriorPower r).subquotient (P j) (P (j + 1)))).subquotient
        S U)).1
  refine ⟨fun U S hQ ↦ ?_, fun T hT hcard ↦ ?_⟩
  · -- a constituent of `⋀^r ρ` is a constituent of some `⋀^j A ⊗ ⋀^{r - j} (ρ / A)`
    obtain ⟨j, hj, U', S', ⟨e₁⟩⟩ :=
      Subrepresentation.exists_subquotient_equiv_of_antitone_chain hPn hP (hP0 ▸ le_top) hQ
    have hjr : j ≤ r := Nat.lt_succ_iff.1 hj
    stop
    obtain ⟨e⟩ := Representation.nonempty_equiv_exteriorPowerFiltration A hjr
    obtain ⟨U'', S'', ⟨e₂⟩⟩ := Subrepresentation.exists_subquotient_equiv_of_equiv e.symm U' S'
    let f := e₂.trans e₁
    obtain ⟨UV, SV, UE, SE, -, -, hV, hE, -, -, heq⟩ :=
      Representation.exists_detWeight_eq_add_of_subquotient_tprod
        (weightCharacter ι (Nat.card K)) W.deg W.frobeniusLift _ _
        (fun UV SV _ ↦ hdetV j UV SV) (fun UE SE _ ↦ hdetE (r - j) UE SE)
        (f.isIrreducible_iff.2 hQ) (hdet hjr U'' S'')
    obtain ⟨T₁, hT₁, hc₁, hs₁⟩ := (ihA j).1 UV SV hV
    obtain ⟨T₂, hT₂, hc₂, hs₂⟩ := (ihQ (r - j)).1 UE SE hE
    refine ⟨T₁ + T₂, hadd ▸ add_le_add hT₁ hT₂, by rw [Multiset.card_add, hc₁, hc₂]; omega, ?_⟩
    rw [Multiset.sum_add, ← hs₁, ← hs₂, ← detWeight_of_equiv ι f,
      detWeight_eq_detWeight_weightCharacter, heq, detWeight_eq_detWeight_weightCharacter,
      detWeight_eq_detWeight_weightCharacter]
  · -- split `T` between `A` and `ρ / A`
    classical
    stop
    rw [hadd] at hT
    have hT₁T : T ∩ W.rankDetWeightMultiset l A.toRepresentation ι ≤ T := Multiset.inter_le_left
    have hT₂ : T - T ∩ W.rankDetWeightMultiset l A.toRepresentation ι ≤
        W.rankDetWeightMultiset l A.quotient ι := by
      refine Multiset.le_iff_count.2 fun a ↦ ?_
      have h := Multiset.le_iff_count.1 hT a
      rw [Multiset.count_add] at h
      rw [Multiset.count_sub, Multiset.count_inter]
      omega
    set T₁ := T ∩ W.rankDetWeightMultiset l A.toRepresentation ι
    have hjr : Multiset.card T₁ ≤ r := hcard ▸ Multiset.card_le_card hT₁T
    have hc₂ : Multiset.card (T - T₁) = r - Multiset.card T₁ := by
      rw [Multiset.card_sub hT₁T, hcard]
    obtain ⟨UV, SV, hV, hs₁⟩ := (ihA (Multiset.card T₁)).2 T₁ Multiset.inter_le_right rfl
    obtain ⟨UE, SE, hE, hs₂⟩ := (ihQ (r - Multiset.card T₁)).2 (T - T₁) hT₂ hc₂
    obtain ⟨U'', S'', -, hQ'', heq⟩ :=
      Representation.exists_isIrreducible_subquotient_tprod_detWeight_eq_add
        (weightCharacter ι (Nat.card K)) W.deg W.frobeniusLift hV hE (hdetV _ UV SV)
        (hdetE _ UE SE) fun U S _ ↦ hdet hjr U S
    obtain ⟨e⟩ := Representation.nonempty_equiv_exteriorPowerFiltration A hjr
    obtain ⟨U', S', ⟨e₂⟩⟩ := Subrepresentation.exists_subquotient_equiv_of_equiv e U'' S''
    obtain ⟨U, S, ⟨e₃⟩⟩ := Subrepresentation.exists_subquotient_equiv_of_subquotient U' S'
    let f := e₃.trans e₂
    refine ⟨U, S, f.isIrreducible_iff.2 hQ'', ?_⟩
    rw [← add_tsub_cancel_of_le hT₁T, Multiset.sum_add, ← hs₁, ← hs₂, ← detWeight_of_equiv ι f,
      detWeight_eq_detWeight_weightCharacter, heq, detWeight_eq_detWeight_weightCharacter,
      detWeight_eq_detWeight_weightCharacter]

end Exterior

end WeilGroup

end AlgebraicGeometry
