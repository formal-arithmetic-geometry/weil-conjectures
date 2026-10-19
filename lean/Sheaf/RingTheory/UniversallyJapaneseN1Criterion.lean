/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Mathlib.RingTheory.FiniteType
public import WeilConjectures.RingTheory.JapaneseDomain
public import WeilConjectures.RingTheory.NagataRing

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# A normalization criterion for universally Japanese rings

Source: Stacks Project, Algebra, Lemma 10.162.3 (Tag 0351),
`lemma-check-universally-japanese`
(blueprint: lem-exc-universally-japanese-n1-criterion).
-/

@[expose] public section

universe u

/-- A commutative ring is universally Japanese if every finite type domain algebra over
it has finite normalization in its fraction field.
Source: Stacks Project, Algebra, Lemma 10.162.3 (Tag 0351),
`lemma-check-universally-japanese`
(blueprint: lem-exc-universally-japanese-n1-criterion).

Proof:
1. Fix a finite type domain algebra `S` over `R` and a finite extension `L` of
   `FractionRing S`. Mathlib's `FiniteDimensional.exists_is_basis_integral` gives a
   finite basis of `L` consisting of elements integral over `S`. Adjoin those elements
   to form a subalgebra `B` of `L`. Finite integral generation makes `B` finite over `S`.
2. For each `z : L`, clear the denominators of its basis coordinates simultaneously.
   For the resulting nonzero `d : S`, the basis expansion expresses `d • z` as an
   `S`-linear combination of the basis, hence as an element of `B`. Since `d` is also
   in `B` and remains nonzero in `L`, the quotient `(d • z) / d` shows that `L` is a
   fraction field of `B`.
3. Finiteness over `S` and finite type over `R` make `B` finite type over `R`.
   As a subring of `L`, it is a domain. Apply the hypothesis to `B`, and transport
   its finite normalization from `FractionRing B` to `L` by the canonical algebra
   equivalence of fraction fields. Transitivity makes this normalization finite over `S`.
4. Because `B` is finite, it is integral over `S`. Transitivity of integrality maps
   the integral closure of `B` in `L` to that of `S` in `L`. This `S`-linear map is
   surjective: every element integral over `S` is integral over `B`. Its target is
   therefore finite over `S`. Varying `L` and `S` proves universal Japaneseness. -/
theorem isUniversallyJapanese_of_forall_isN1 (R : Type u) [CommRing R]
    (h : ∀ (S : Type u) [CommRing S] [IsDomain S] [Algebra R S]
      [Algebra.FiniteType R S], IsN1 S (FractionRing S)) :
    IsUniversallyJapanese R := by
  classical
  intro S _ _ _ _ L _ _ _ _ _
  obtain ⟨t, e, he⟩ := FiniteDimensional.exists_is_basis_integral S (FractionRing S) L
  let B := Algebra.adjoin S (Set.range e)
  have : Module.Finite S B :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range e)
      (by rintro _ ⟨i, rfl⟩; exact he i)
  have : IsFractionRing B L := IsFractionRing.of_field B L (fun z ↦ by
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors S) (fun i ↦ e.repr z i)
    choose a ha using hd
    have hd0 : (d : S) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
    have hdm : algebraMap S L d ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply S (FractionRing S) L]
      exact (map_ne_zero_iff (algebraMap (FractionRing S) L) (RingHom.injective _)).mpr
        ((map_ne_zero_iff (algebraMap S (FractionRing S))
          (IsFractionRing.injective S (FractionRing S))).mpr hd0)
    have hdz : (d : S) • z ∈ B := by
      rw [← e.sum_repr z, Finset.smul_sum]
      apply B.sum_mem
      intro i _
      rw [← smul_assoc, ← ha i, algebraMap_smul]
      exact B.smul_mem (Algebra.subset_adjoin ⟨i, rfl⟩) (a i)
    refine ⟨(⟨(d : S) • z, hdz⟩ : B),
      (⟨algebraMap S L d, B.algebraMap_mem d⟩ : B), ?_⟩
    change z = ((d : S) • z) / algebraMap S L d
    rw [Algebra.smul_def, mul_div_cancel_left₀ _ hdm])
  let : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S L := .of_algebraMap_eq' rfl
  have : Algebra.FiniteType R B := Algebra.FiniteType.trans
    (S := S) inferInstance inferInstance
  have : Module.Finite B (integralClosure B (FractionRing B)) := h B
  have : Module.Finite B (integralClosure B L) := Module.Finite.equiv
    ((IsLocalization.algEquiv (nonZeroDivisors B) (FractionRing B) L).mapIntegralClosure
      ).toLinearEquiv
  have : Module.Finite S (integralClosure B L) := Module.Finite.trans B _
  let q : integralClosure B L →ₗ[S] integralClosure S L :=
    { toFun := fun z ↦ ⟨z.1, isIntegral_trans z.1 z.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hq : Function.Surjective q := by
    intro z
    exact ⟨⟨z.1, z.2.tower_top⟩, rfl⟩
  exact Module.Finite.of_surjective q hq
