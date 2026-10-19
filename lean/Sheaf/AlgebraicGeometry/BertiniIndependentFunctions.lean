/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q138
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Tactic.Convert
import Mathlib.Tactic.NormNum
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
import Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg
import Sheaf.RingTheory.FiniteTypeFibreComponentLowerBound

/-!
# Independent generic linear combinations from a codimension-two intersection

Source: Stacks Project, More on Morphisms, Tag 0G4E, `lemma-algebraically-independent`
(blueprint: lem-zl-bertini-independent-functions).

The component is a subset of the common zero locus with its subspace topology.
Its dimension condition is written additively to avoid truncated subtraction.
The family is indexed by `Fin n ⊕ Fin 2`: the variables, the universal linear
combination, and the scalar linear combination, all in `Frac(Frac(A)[x₁,...,xₙ])`.
-/

@[expose] public section

universe u v

open scoped BigOperators

namespace Algebra

/-- A codimension-two component of `V(g₁,g₂)` supplies an algebraically independent
family consisting of the variables, their `g`-linear combination, and a scalar
linear combination of the `g i`.

Source: Stacks Project, More on Morphisms, Tag 0G4E, `lemma-algebraically-independent`
(blueprint: lem-zl-bertini-independent-functions).

Proof:
1. Set C = A[x₁,...,xₙ], h = sum gᵢxᵢ, and B = k[X₁,...,Xₙ,Y,Z]. Map B to C by
   Xᵢ ↦ xᵢ, Y ↦ h, Z ↦ g₂. Both polynomial rings are domains. The inclusions
   A → Frac(A) and C → Frac(A)[x₁,...,xₙ] → Frac(Frac(A)[x₁,...,xₙ]) are injective,
   so independence of the indicated family is equivalent to this map having zero kernel.
2. Write d = dim A, finite by lem-weil-pbc-finite-type-domain-dimension-trdeg.
   Finite type implies Noetherianity (lem-wf-affine-noetherian-components).
   The polynomial dimension theorem (lem-sf-noetherian-polynomial-dimension) gives
   dim C = d+n and dim B = n+2, since dim k = 0.
3. At the rational maximal ideal m = (X₁-1,X₂,...,Xₙ,Y,Z), the extended ideal in C
   equals (x₁-1,x₂,...,xₙ,g₁,g₂), using h-g₁ = g₁(x₁-1) + sum_{i>1} gᵢxᵢ.
   Evaluation identifies C/mC with A/(g₁,g₂). Its spectrum is homeomorphic to
   V(g₁,g₂), so the hypothesis supplies a fibre component of dimension d-2.
4. If the kernel P were nonzero, it would be a proper prime ideal. Prepending (0)
   to any prime chain above P shows dim(B/P) ≤ n+1.
5. Apply lem-zl-finite-type-fibre-component-lower-bound to B → C and m. The chosen
   component would have dimension at least dim C - dim(B/P) ≥ d-1, contradicting
   dimension d-2. Hence the kernel is zero.
6. Choose c₂ = 1 and cᵢ = 0 for i ≠ 2, so sum cᵢgᵢ = g₂. The zero-kernel conclusion
   gives the asserted algebraic independence. Only 0 and 1 are used, including over finite k.
-/
theorem bertini_independent_functions
    (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Algebra k A] [FiniteType k A] [IsDomain A]
    (n : ℕ) (hn : 2 ≤ n) (g : Fin n → A)
    (hcomp : ∃ W : Set (PrimeSpectrum.zeroLocus
        ({g ⟨0, Nat.zero_lt_of_lt hn⟩, g ⟨1, hn⟩} : Set A)),
      W ∈ irreducibleComponents (PrimeSpectrum.zeroLocus
        ({g ⟨0, Nat.zero_lt_of_lt hn⟩, g ⟨1, hn⟩} : Set A)) ∧
      topologicalKrullDim W + 2 = ringKrullDim A) :
    ∃ c : Fin n → k,
      AlgebraicIndependent k
        (fun j : Fin n ⊕ Fin 2 ↦
          algebraMap (MvPolynomial (Fin n) (FractionRing A))
            (FractionRing (MvPolynomial (Fin n) (FractionRing A)))
            (match j with
            | Sum.inl i => MvPolynomial.X i
            | Sum.inr i =>
                Fin.cases
                  (∑ i : Fin n,
                    MvPolynomial.C (algebraMap A (FractionRing A) (g i)) *
                      MvPolynomial.X i)
                  (fun _ ↦ MvPolynomial.C
                    (∑ i : Fin n,
                      algebraMap k (FractionRing A) (c i) *
                        algebraMap A (FractionRing A) (g i))) i)) := by
  classical
  let i₀ : Fin n := ⟨0, Nat.zero_lt_of_lt hn⟩
  let i₁ : Fin n := ⟨1, hn⟩
  let a : Fin n → k := fun i ↦ if i = i₀ then 1 else 0
  let b : Fin n ⊕ Fin 2 → k := Sum.elim a (fun _ ↦ 0)
  let h : (MvPolynomial (Fin n) A) := ∑ i, MvPolynomial.C (g i) * MvPolynomial.X i
  let f : Fin n ⊕ Fin 2 → (MvPolynomial (Fin n) A) := Sum.elim MvPolynomial.X
    (fun j ↦ Fin.cases h (fun _ ↦ MvPolynomial.C (g i₁)) j)
  let φ : (MvPolynomial (Fin n ⊕ Fin 2) k) →ₐ[k] (MvPolynomial (Fin n) A) :=
    MvPolynomial.aeval f
  let ev : (MvPolynomial (Fin n ⊕ Fin 2) k) →+* k := MvPolynomial.eval b
  let m := RingHom.ker ev
  let J := Ideal.map φ.toRingHom m
  let I : Ideal A := Ideal.span ({g i₀, g i₁} : Set A)
  let q := Ideal.Quotient.mk I
  let e : (MvPolynomial (Fin n) A) →+* A ⧸ I :=
    MvPolynomial.eval₂Hom q (fun i ↦ q (algebraMap k A (a i)))
  have hg₀ : q (g i₀) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (by simp))
  have hg₁ : q (g i₁) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (by simp))
  have heh : e h = 0 := by
    simp [e, h, a, apply_ite, hg₀]
  have heφ : e.comp φ.toRingHom = (algebraMap k (A ⧸ I)).comp ev := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change e (φ (MvPolynomial.C r)) = algebraMap k (A ⧸ I) (ev (MvPolynomial.C r))
      simp only [φ, MvPolynomial.aeval_C, MvPolynomial.algebraMap_apply,
        e, MvPolynomial.eval₂Hom_C, ev, MvPolynomial.eval_C]
      rfl
    · intro j
      change e (φ (MvPolynomial.X j)) = algebraMap k (A ⧸ I) (ev (MvPolynomial.X j))
      simp only [φ, MvPolynomial.aeval_X, ev, MvPolynomial.eval_X]
      rcases j with i | j
      · simp only [f, Sum.elim_inl, e, MvPolynomial.eval₂Hom_X', b]
        rfl
      · refine Fin.cases ?_ (fun j ↦ ?_) j
        · simpa only [f, Sum.elim_inr, Fin.cases_zero, b, map_zero] using heh
        · have hj : j = 0 := Subsingleton.elim _ _
          subst j
          simpa only [f, Sum.elim_inr, Fin.cases_succ, e, MvPolynomial.eval₂Hom_C,
            b, map_zero] using hg₁
  have hJe : J ≤ RingHom.ker e := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    change e (φ p) = 0
    change ev p = 0 at hp
    have hh := DFunLike.congr_fun heφ p
    simpa [hp] using hh
  let E : (MvPolynomial (Fin n) A) ⧸ J →+* A ⧸ I := Ideal.Quotient.lift J e hJe
  have hrel (j : Fin n ⊕ Fin 2) :
      φ (MvPolynomial.X j - MvPolynomial.C (b j)) ∈ J := by
    apply Ideal.mem_map_of_mem
    change ev _ = 0
    simp only [ev, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_self]
  have hx (i : Fin n) :
      Ideal.Quotient.mk J (MvPolynomial.X i) =
        Ideal.Quotient.mk J (MvPolynomial.C (algebraMap k A (a i))) := by
    apply sub_eq_zero.mp
    rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    simpa only [φ, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, f,
      Sum.elim_inl, b, MvPolynomial.algebraMap_apply] using hrel (Sum.inl i)
  have hhJ : h ∈ J := by
    simpa only [φ, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, f,
      Sum.elim_inr, Fin.cases_zero, b, map_zero, sub_zero] using hrel (Sum.inr 0)
  have hg₁J : MvPolynomial.C (g i₁) ∈ J := by
    simpa only [φ, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, f,
      Sum.elim_inr, Fin.cases_zero, Fin.cases_succ, b, map_zero, sub_zero]
      using hrel (Sum.inr (Fin.succ 0))
  have hg₀J : MvPolynomial.C (g i₀) ∈ J := by
    have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hhJ
    have hs : Ideal.Quotient.mk J h = Ideal.Quotient.mk J (MvPolynomial.C (g i₀)) := by
      simp only [h, map_sum, map_mul, hx]
      simp [a, Finset.sum_ite_eq']
    rw [hs] at hh
    exact Ideal.Quotient.eq_zero_iff_mem.mp hh
  let inc : A →+* (MvPolynomial (Fin n) A) ⧸ J := (Ideal.Quotient.mk J).comp MvPolynomial.C
  have hIinc : I ≤ RingHom.ker inc := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases hx with rfl | hx
    · exact Ideal.Quotient.eq_zero_iff_mem.mpr hg₀J
    · have hhx : x = g i₁ := Set.mem_singleton_iff.mp hx
      subst x
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hg₁J
  let F : A ⧸ I →+* (MvPolynomial (Fin n) A) ⧸ J := Ideal.Quotient.lift I inc hIinc
  have hFE : F.comp E = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [F, E, e, inc, q]
    · intro i
      simp only [RingHom.comp_apply, E, Ideal.Quotient.lift_mk,
        e, MvPolynomial.eval₂Hom_X', RingHom.id_apply]
      simpa only [F, q, Ideal.Quotient.lift_mk, inc, RingHom.comp_apply] using (hx i).symm
  have hEF : E.comp F = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    simp [F, E, e, inc, q]
  let eqv : (MvPolynomial (Fin n) A) ⧸ J ≃+* A ⧸ I :=
    { E with
      invFun := F
      left_inv := fun x ↦ DFunLike.congr_fun hFE x
      right_inv := fun x ↦ DFunLike.congr_fun hEF x }
  have hqrange : Set.range (PrimeSpectrum.comap q) =
      PrimeSpectrum.zeroLocus ({g i₀, g i₁} : Set A) := by
    rw [range_comap_of_surjective (A ⧸ I) q
      Ideal.Quotient.mk_surjective]
    simp only [q, Ideal.mk_ker, I, PrimeSpectrum.zeroLocus_span]
  let eqz : PrimeSpectrum (A ⧸ I) ≃ₜ
      PrimeSpectrum.zeroLocus ({g i₀, g i₁} : Set A) :=
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective (A ⧸ I) q
      Ideal.Quotient.mk_surjective).isEmbedding.toHomeomorph.trans
        (Homeomorph.setCongr hqrange)
  let eh := (PrimeSpectrum.homeomorphOfRingEquiv eqv).trans eqz
  obtain ⟨W, hW, hWd⟩ := hcomp
  change W ∈ irreducibleComponents
    (PrimeSpectrum.zeroLocus ({g i₀, g i₁} : Set A)) at hW
  let W' := eh ⁻¹' W
  have hW' : W' ∈ irreducibleComponents
      (PrimeSpectrum ((MvPolynomial (Fin n) A) ⧸ J)) := by
    apply preimage_mem_irreducibleComponents hW eh.isOpenEmbedding
    simpa only [eh.surjective.range_eq, Set.inter_univ] using hW.1.nonempty
  have hdim : topologicalKrullDim W' = topologicalKrullDim W := by
    let ew : W' ≃ₜ W := eh.subtype (fun _ ↦ Iff.rfl)
    exact ew.isHomeomorph.topologicalKrullDim_eq ew
  have hev : Function.Surjective ev := fun r ↦ ⟨MvPolynomial.C r, by simp [ev]⟩
  have hm : m.IsMaximal := RingHom.ker_isMaximal_of_surjective ev hev
  have hmk : Function.Bijective (algebraMap k ((MvPolynomial (Fin n ⊕ Fin 2) k) ⧸ m)) := by
    let em : (MvPolynomial (Fin n ⊕ Fin 2) k) ⧸ m ≃+* k :=
      ev.quotientKerEquivOfSurjective hev
    have hem (r : k) : em (algebraMap k _ r) = r := by
      change em (Ideal.Quotient.mk m (MvPolynomial.C r)) = r
      exact (RingHom.quotientKerEquivOfSurjective_apply_mk hev (MvPolynomial.C r)).trans
        (MvPolynomial.eval_C r)
    refine ⟨fun x y hxy ↦ ?_, fun x ↦ ?_⟩
    · simpa only [hem] using congrArg em hxy
    · exact ⟨em x, em.injective (hem (em x))⟩
  have : FiniteType k (MvPolynomial (Fin n) A) :=
    FiniteType.trans (inferInstance : FiniteType k A) inferInstance
  obtain ⟨dC, dP, hdC, hdP, hbound⟩ := finiteType_fibre_component_lower_bound
    k (MvPolynomial (Fin n ⊕ Fin 2) k) (MvPolynomial (Fin n) A) φ m hm hmk
  obtain ⟨d, hd, _, _⟩ := finiteType_domain_ringKrullDim_eq_trdeg (k := k) (S := A)
  have : IsNoetherianRing A := FiniteType.isNoetherianRing k A
  have hdC' : dC = d + n := by
    have hc := MvPolynomial.ringKrullDim_of_isNoetherianRing (R := A) (ι := Fin n)
    rw [hdC, hd] at hc
    norm_num only [Nat.card_fin, ← Nat.cast_add] at hc
    exact_mod_cast hc
  have hinj : Function.Injective φ.toRingHom := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hker
    obtain ⟨r, hr, hr0⟩ := (Submodule.ne_bot_iff _).mp hker
    have hdrop := ringKrullDim_succ_le_of_surjective
      (Ideal.Quotient.mk (RingHom.ker φ.toRingHom)) Ideal.Quotient.mk_surjective
      (mem_nonZeroDivisors_of_ne_zero hr0) (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
    rw [hdP, MvPolynomial.ringKrullDim_of_isNoetherianRing] at hdrop
    simp only [ringKrullDim_eq_zero_of_field, zero_add, Nat.card_eq_fintype_card,
      Fintype.card_sum, Fintype.card_fin] at hdrop
    have hdrop' : dP + 1 ≤ n + 2 := by exact_mod_cast hdrop
    have hb : ((dC - dP : ℕ) : WithBot ℕ∞) + 2 ≤ topologicalKrullDim W' + 2 :=
      add_le_add (hbound W' hW') le_rfl
    rw [hdim, hWd, hd] at hb
    have hb' : dC - dP + 2 ≤ d := by exact_mod_cast hb
    omega
  have hf : AlgebraicIndependent k f := hinj
  let μ : MvPolynomial (Fin n) A →ₐ[k] MvPolynomial (Fin n) (FractionRing A) :=
    MvPolynomial.mapAlgHom (IsScalarTower.toAlgHom k A (FractionRing A))
  have hμ : Function.Injective μ :=
    MvPolynomial.map_injective _ (IsFractionRing.injective A (FractionRing A))
  have hloc := IsFractionRing.injective
    (MvPolynomial (Fin n) (FractionRing A))
    (FractionRing (MvPolynomial (Fin n) (FractionRing A)))
  have hind := (hf.map' hμ).map'
    (f := IsScalarTower.toAlgHom k (MvPolynomial (Fin n) (FractionRing A))
      (FractionRing (MvPolynomial (Fin n) (FractionRing A)))) hloc
  refine ⟨(fun i ↦ if i = i₁ then 1 else 0), ?_⟩
  convert hind using 1
  funext j
  apply congrArg (algebraMap (MvPolynomial (Fin n) (FractionRing A))
    (FractionRing (MvPolynomial (Fin n) (FractionRing A))))
  rcases j with i | j
  · simp [μ, f]
  · refine Fin.cases ?_ (fun j ↦ ?_) j
    · simp [μ, f, h]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change MvPolynomial.C (∑ i : Fin n,
        algebraMap k (FractionRing A) (if i = i₁ then 1 else 0) *
          algebraMap A (FractionRing A) (g i)) =
        μ (MvPolynomial.C (g i₁))
      simp [μ, apply_ite]

end Algebra
