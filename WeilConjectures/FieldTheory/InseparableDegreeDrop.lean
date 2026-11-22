/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.Mathlib.RingTheory.DedekindDomain.IntegralClosure
import WeilConjectures.FieldTheory.CoefficientRootExtension

@[expose] public section
set_option autoImplicit false
universe w
namespace FieldExtension

-- Choose the penultimate element of a shortest Frobenius chain (Stacks 04KM).
private theorem beta_exists (E K : Type w) [Field E] [Field K] [Algebra E K]
    [Module.Finite E K] (p : ℕ) [ExpChar E p]
    (hne : Field.finInsepDegree E K ≠ 1) :
    ∃ β : K, β ∉ separableClosure E K ∧ β ^ p ∈ separableClosure E K := by
  classical
  have htop : separableClosure E K ≠ ⊤ := by
    intro h
    exact hne ((isSeparable_iff_finInsepDegree_eq_one E K).mp
      ((separableClosure.eq_top_iff E K).mp h))
  obtain ⟨x, hx⟩ : ∃ x : K, x ∉ separableClosure E K := by
    by_contra! h
    exact htop (top_unique (fun x _ ↦ h x))
  have : ExpChar (separableClosure E K) p :=
    expChar_of_injective_algebraMap (algebraMap E (separableClosure E K)).injective p
  have hex (y : K) : ∃ n : ℕ, y ^ p ^ n ∈ separableClosure E K := by
    obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem (separableClosure E K) p y
    exact ⟨n, ha ▸ a.property⟩
  let n := Nat.find (hex x)
  have hn : x ^ p ^ n ∈ separableClosure E K := Nat.find_spec (hex x)
  have hn0 : n ≠ 0 := by
    intro h
    exact hx (by simpa [h] using hn)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨x ^ p ^ m, ?_, ?_⟩
  · exact Nat.find_min (hex x) (by omega)
  · simpa [hm, pow_succ, pow_mul] using hn

-- Specialize the proved coefficient criterion to one Frobenius step.
private theorem separable_of_coeff_root
    (E E₁ K L : Type w) [Field E] [Field E₁] [Field K] [Field L]
    [Algebra E K] [Algebra K L] [Algebra E L] [IsScalarTower E K L]
    [Algebra E E₁] [Algebra E₁ L] [IsScalarTower E E₁ L]
    (p : ℕ) [Fact p.Prime] [CharP E p]
    (β : K) (hβ : IsSeparable E (β ^ p))
    (hcoeff : ∀ n : ℕ, ∃ b : E₁,
      algebraMap E E₁ ((minpoly E (β ^ p)).coeff n) = b ^ p) :
    IsSeparable E₁ (algebraMap K L β) := by
  let f := IsScalarTower.toAlgHom E K L
  have : ExpChar E₁ p := expChar_of_injective_algebraMap (algebraMap E E₁).injective p
  change IsSeparable E₁ (f β)
  apply IsSeparable.of_pow_of_coeffs (K := E) p 1
  · simpa only [pow_one, ← map_pow] using hβ.map f f.injective
  · simp only [pow_one, ← map_pow, minpoly.algHom_eq f f.injective]
    intro c hc
    obtain ⟨n, hn, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
    obtain ⟨b, hb⟩ := hcoeff n
    exact ⟨b, hb.symm⟩

-- Apply the compositum rank bound to the field range of K in L.
private theorem compositum_finrank_le
    (F K S L : Type w) [Field F] [Field K] [Field S] [Field L]
    [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [Algebra F S] [Algebra S L] [IsScalarTower F S L]
    [Module.Finite F K]
    (hcomp : IntermediateField.adjoin S (Set.range (algebraMap K L)) = ⊤) :
    Module.Finite S L ∧ Module.finrank S L ≤ Module.finrank F K := by
  let f := IsScalarTower.toAlgHom F K L
  have : Module.Finite F f.fieldRange := f.equivFieldRange.toLinearEquiv.finiteDimensional
  have hr := IntermediateField.adjoin_rank_le_of_isAlgebraic_right S f.fieldRange
  have heq : Module.rank F f.fieldRange = Module.rank F K :=
    f.equivFieldRange.toLinearEquiv.rank_eq.symm
  rw [heq] at hr
  have hc : IntermediateField.adjoin S (f.fieldRange : Set L) = ⊤ := hcomp
  rw [hc, IntermediateField.rank_top'] at hr
  exact ⟨Module.rank_lt_aleph0_iff.mp (hr.trans_lt (Module.rank_lt_aleph0 F K)),
    Cardinal.toNat_le_toNat hr (Module.rank_lt_aleph0 F K)⟩

-- Becoming separable after a compositum base change forces a strict degree drop.
private theorem insep_lt_of_new_separable_element
    (E E₁ K L : Type w) [Field E] [Field E₁] [Field K] [Field L]
    [Algebra E K] [Algebra K L] [Algebra E L] [IsScalarTower E K L]
    [Algebra E E₁] [Algebra E₁ L] [IsScalarTower E E₁ L]
    [Module.Finite E K]
    (hcomp : IntermediateField.adjoin E₁ (Set.range (algebraMap K L)) = ⊤)
    (β : K) (hβ : β ∉ separableClosure E K)
    (hβ' : IsSeparable E₁ (algebraMap K L β)) :
    Field.finInsepDegree E₁ L < Field.finInsepDegree E K := by
  let S := separableClosure E₁ L
  let f := IsScalarTower.toAlgHom E K L
  let T : IntermediateField E K := (S.restrictScalars E).comap f
  have hKs : separableClosure E K ≤ T := by
    intro x hx
    exact ((mem_separableClosure_iff.mp hx).map f f.injective).tower_top E₁
  have hβT : β ∈ T := hβ'
  let A : IntermediateField E K := separableClosure E K ⊔ IntermediateField.adjoin E {β}
  have hAT : A ≤ T := sup_le hKs (IntermediateField.adjoin_simple_le_iff.mpr hβT)
  have hstrict : separableClosure E K < A := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    have hβA : β ∈ A :=
      (le_sup_right : IntermediateField.adjoin E {β} ≤ A)
        (IntermediateField.mem_adjoin_simple_self E β)
    exact hβ (heq ▸ hβA)
  let g : A →+* S := (algebraMap K L).comp A.val.toRingHom |>.codRestrict S.toSubring
    (fun a ↦ hAT a.property)
  let : Algebra A S := g.toAlgebra
  have : IsScalarTower A S L := .of_algebraMap_eq' rfl
  have hcompS : IntermediateField.adjoin S (Set.range (algebraMap K L)) = ⊤ := by
    apply top_unique
    intro x _
    have hle : IntermediateField.adjoin E₁ (Set.range (algebraMap K L)) ≤
        (IntermediateField.adjoin S (Set.range (algebraMap K L))).restrictScalars E₁ :=
      IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin S _)
    exact hle (hcomp ▸ (IntermediateField.mem_top : x ∈ (⊤ : IntermediateField E₁ L)))
  have hbound := compositum_finrank_le A K S L hcompS
  exact hbound.2.trans_lt (IntermediateField.finrank_lt_of_gt hstrict)

-- The existing existential instance binders are used implicitly; keep its signature unchanged.
set_option linter.unusedVariables false in
/-- One coefficient-root construction strictly decreases the inseparable degree.
Source: Stacks Project, Algebra, Tag 04KM, the induction step. -/
theorem exists_inseparableDegree_drop
    (k K : Type w) [Field k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG) (s : Finset K)
    (hs : IsTranscendenceBasis k ((↑) : s → K))
    [Module.Finite (IntermediateField.adjoin k (s : Set K)) K]
    (hne : Field.finInsepDegree (IntermediateField.adjoin k (s : Set K)) K ≠ 1) :
    ∃ (l : Type w) (hl : Field l) (akl : Algebra k l)
      (L : Type w) (hL : Field L) (aKL : Algebra K L) (alL : Algebra l L)
      (akL : Algebra k L) (htl : IsScalarTower k l L) (htK : IsScalarTower k K L),
      Module.Finite k l ∧ IsPurelyInseparable k l ∧
      Module.Finite K L ∧ IsPurelyInseparable K L ∧
      (⊤ : IntermediateField l L).FG ∧
      ∃ t : Finset L, IsTranscendenceBasis l ((↑) : t → L) ∧
        Module.Finite (IntermediateField.adjoin l (t : Set L)) L ∧
        Field.finInsepDegree (IntermediateField.adjoin l (t : Set L)) L <
          Field.finInsepDegree (IntermediateField.adjoin k (s : Set K)) K := by
  obtain ⟨p, hp⟩ := ExpChar.exists k
  have : ExpChar (IntermediateField.adjoin k (s : Set K)) p :=
    expChar_of_injective_algebraMap
      (algebraMap k (IntermediateField.adjoin k (s : Set K))).injective p
  obtain ⟨β, hβ, hβp⟩ := beta_exists (IntermediateField.adjoin k (s : Set K)) K p hne
  cases hp with
  | zero => exact (hβ (by simpa using hβp)).elim
  | prime hprime =>
    have : Fact p.Prime := ⟨hprime⟩
    obtain ⟨l, hl, akl, L, hL, aKL, alL, akL, htl, htK,
      hkl, hpi, hKL, hPI, t, ht, a, htw, hcoeff, hcomp⟩ :=
      exists_coefficientRoot_extension k K s hs.1 p
        (minpoly (IntermediateField.adjoin k (s : Set K)) (β ^ p))
    have : CharP (IntermediateField.adjoin k (s : Set K)) p :=
      charP_of_injective_algebraMap
        (algebraMap k (IntermediateField.adjoin k (s : Set K))).injective p
    have hfin : Module.Finite (IntermediateField.adjoin l (t : Set L)) L :=
      (compositum_finrank_le (IntermediateField.adjoin k (s : Set K)) K
        (IntermediateField.adjoin l (t : Set L)) L hcomp).1
    have htb : IsTranscendenceBasis l ((↑) : t → L) := by
      apply ht.isTranscendenceBasis_iff_isAlgebraic.mpr
      have halg : Algebra.IsAlgebraic (Algebra.adjoin l (t : Set L)) L :=
        IntermediateField.isAlgebraic_adjoin_iff_top.mp inferInstance
      rw [show Set.range ((↑) : t → L) = (t : Set L) by ext x; simp]
      exact halg
    have hfgL : (⊤ : IntermediateField l L).FG := by
      have : Algebra.EssFiniteType k K := IntermediateField.fg_top_iff.mp hfg
      have : Algebra.EssFiniteType k L := Algebra.EssFiniteType.comp k K L
      have : Algebra.EssFiniteType l L := Algebra.EssFiniteType.of_comp k l L
      exact IntermediateField.fg_top l L
    have hnew := separable_of_coeff_root
      (IntermediateField.adjoin k (s : Set K)) (IntermediateField.adjoin l (t : Set L))
      K L p β (mem_separableClosure_iff.mp hβp) hcoeff
    refine ⟨l, hl, akl, L, hL, aKL, alL, akL, htl, htK,
      hkl, hpi, hKL, hPI, hfgL, t, htb, hfin, ?_⟩
    exact insep_lt_of_new_separable_element
      (IntermediateField.adjoin k (s : Set K)) (IntermediateField.adjoin l (t : Set L))
      K L hcomp β hβ hnew

end FieldExtension
