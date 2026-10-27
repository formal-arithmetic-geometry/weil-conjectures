/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NX
-/
module

public import Mathlib.Algebra.GradedMulAction
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.RingTheory.NoetherianAlgebraModuleGenericFreeness
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Simultaneous generic ranks of graded pieces after a prime quotient

Source: Stacks Project, Algebra, Tags 051R and 00NX, with the graded and
quotient/localization fibre adaptation in the DAG proof
(blueprint: lem-sfb-graded-quotient-generic-ranks).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct DirectSum

namespace Module

/-- After any prime quotient, one localization makes the entire graded module free and
all its finite graded pieces finite projective of constant fibre dimension simultaneously.
Tensor factors are written with the coefficient algebra on the left, using the canonical
commutativity isomorphism with the right-factor convention of the source.

Source: Stacks Project, Algebra, Tag 051R, lemma-generic-flatness-Noetherian, and Tag 00NX,
lemma-finite-projective, clauses (3) and (8); graded quotient/localization adaptation
(blueprint: lem-sfb-graded-quotient-generic-ranks).

Proof: (1) The prime quotient R=A/I is a nonzero Noetherian domain. Algebra and module
finite generators base-change to D=R tensor C and N=R tensor M, and each piece remains
finite. Tensor the grading decomposition; its inverse on a degree-d pure tensor is the
inclusion of that homogeneous element. These maps are inverse on pure tensors, and the
multiplication and action still add degrees.
(2) Apply lem-pur-noetherian-algebra-module-generic-freeness to R,D,N to obtain a single
nonzero a such that N_a is free; its basis may be infinite.
(3) The degree inclusion and projection localize to a retraction of N_a onto each P_d.
The images of finitely many generators of P_d involve finitely many elements of a basis
of N_a. Their union of supports gives a finite free submodule through which the inclusion
factors, and restricting the projection gives the displayed finite-free retraction.
Tag 00NX makes each P_d finite projective.
(4) Apply lem-weil-pbc-finite-projective-rank-locally-constant: the stalk ranks are locally
constant and equal the residue-field fibre dimensions, as seen by reducing a local basis.
(5) Since R_a is a domain, every nonempty basic open contains its generic point. Each
locally constant rank function is therefore constant, with value r(d) at the generic point.
All degrees use the same a.
(6) A prime p containing I and avoiding a in A/I corresponds to the prime q of R_a whose
contraction is p. Fractions identify both residue fields with Frac(A/p); thus the canonical
residue-field map is an isomorphism.
(7) The fibre map sends k tensor m to e(k) tensor ((1 tensor m)/1). Its inverse sends
u tensor ((t tensor m)/a^j) to e.symm(t*a^(-j)*u) tensor m, with t and a interpreted in
the residue field. Balanced tensor and localization relations make these maps well defined
and inverse. Hence every original degree fibre has dimension r(d) on this same open. -/
theorem graded_quotient_generic_ranks
    {A : Type u} {C : Type v} {M : Type w}
    [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
    [AddCommGroup M] [Module C M] [Module A M]
    [IsScalarTower A C M] [Module.Finite C M]
    (𝒞 : ℕ → Submodule A C) (ℳ : ℕ → Submodule A M)
    [GradedAlgebra 𝒞] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒞 ℳ]
    (hfiniteType : (algebraMap A C).FiniteType)
    (hA : Function.Injective (algebraMap A C))
    (hzero : 𝒞 0 = LinearMap.range (Algebra.linearMap A C))
    [∀ d : ℕ, Module.Finite A (ℳ d)] (I : Ideal A) [I.IsPrime] :
    (∃ e : ((A ⧸ I) ⊗[A] M) ≃ₗ[A ⧸ I] (⨁ d : ℕ, (A ⧸ I) ⊗[A] (ℳ d)),
      ∀ (d : ℕ) (t : A ⧸ I) (m : ℳ d),
        e.symm (DirectSum.lof (A ⧸ I) ℕ (fun j ↦ (A ⧸ I) ⊗[A] (ℳ j)) d
          (t ⊗ₜ[A] m)) = t ⊗ₜ[A] (m : M)) ∧
    ∃ a : A ⧸ I, a ≠ 0 ∧ ∃ r : ℕ → ℕ,
      Module.Free (Localization.Away a) (LocalizedModule.Away a ((A ⧸ I) ⊗[A] M)) ∧
      (∀ d : ℕ,
        (∃ n : ℕ,
          ∃ i : LocalizedModule.Away a ((A ⧸ I) ⊗[A] (ℳ d)) →ₗ[Localization.Away a]
              (Fin n → Localization.Away a),
          ∃ p : (Fin n → Localization.Away a) →ₗ[Localization.Away a]
              LocalizedModule.Away a ((A ⧸ I) ⊗[A] (ℳ d)),
            p.comp i = LinearMap.id) ∧
        Module.Finite (Localization.Away a)
          (LocalizedModule.Away a ((A ⧸ I) ⊗[A] (ℳ d))) ∧
        Module.Projective (Localization.Away a)
          (LocalizedModule.Away a ((A ⧸ I) ⊗[A] (ℳ d))) ∧
        ∀ q : PrimeSpectrum (Localization.Away a),
          Module.finrank q.asIdeal.ResidueField
            (q.asIdeal.ResidueField ⊗[Localization.Away a]
              LocalizedModule.Away a ((A ⧸ I) ⊗[A] (ℳ d))) = r d) ∧
      ∀ p : PrimeSpectrum A, I ≤ p.asIdeal →
        a ∉ Ideal.map (Ideal.Quotient.mk I) p.asIdeal →
        ∃ q : PrimeSpectrum (Localization.Away a),
        ∃ hq : p.asIdeal = Ideal.comap (algebraMap A (Localization.Away a)) q.asIdeal,
        ∃ e : p.asIdeal.ResidueField ≃+* q.asIdeal.ResidueField,
          e.toRingHom = Ideal.ResidueField.map p.asIdeal q.asIdeal
            (algebraMap A (Localization.Away a)) hq ∧
          ∀ d : ℕ,
            (∃ E : (p.asIdeal.ResidueField ⊗[A] (ℳ d)) ≃+
                (q.asIdeal.ResidueField ⊗[Localization.Away a]
                  LocalizedModule.Away a ((A ⧸ I) ⊗[A] (ℳ d))),
              (∀ (k : p.asIdeal.ResidueField) (x : p.asIdeal.ResidueField ⊗[A] (ℳ d)),
                E (k • x) = e k • E x) ∧
              ∀ (k : p.asIdeal.ResidueField) (m : ℳ d),
                E (k ⊗ₜ[A] m) = e k ⊗ₜ[Localization.Away a]
                  (LocalizedModule.mkLinearMap (Submonoid.powers a)
                    ((A ⧸ I) ⊗[A] (ℳ d)) ((1 : A ⧸ I) ⊗ₜ[A] m))) ∧
            Module.finrank p.asIdeal.ResidueField
              (p.asIdeal.ResidueField ⊗[A] (ℳ d)) = r d := by
  sorry

end Module
