/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.InertiaStrictHenselization
public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Strict-local inertia: RingCore

Source: Stacks Project, Tag 0BSW
(blueprint: lem-dl-a1-strict-local-inertia-identification-ring-core).
-/

@[expose] public section
set_option autoImplicit false
universe u

/-- The strict-local fraction field identifies with the inertia fixed field.

Source: Stacks Project, pione.tex, Tag 0BSW, setup and first paragraph of the proof
(blueprint: lem-dl-a1-strict-local-inertia-identification-ring-core).

Proof (Steps 1--7 of the parent argument):
1. Choose the residue separable closure `K` specifying `C`. The triples-presentation lemma and
   the strict-henselization triples lemma make `C` a local filtered colimit of etale
   `A`-algebras, henselian, with residue field `K`; write `n` for its maximal ideal.
2. For a stage `S → C`, `F ⊗_A S` is etale over `F`, a finite product of finite separable
   field extensions; its map to `E` selects one factor. So every element of `C`, and by the
   relative separable closure every quotient, is separable algebraic over `F`: `E / F` is
   separable algebraic, `C[(A \ 0)⁻¹] = E`, and the separable-extension embedding lemma gives an
   `F`-embedding `E → Ω`.
3. Put `T = B_Q`. The integral-closure lemma gives `Frac B = Ω` with `B` normal; the Gabber
   quotient-localization lemma (ideal `0`) makes `T` strictly henselian with residue field
   `L = B / Q`, algebraic over `κ`. Embed `K` into `L` over `κ`; the map-into-henselian-colimit
   lemma gives a unique local `A`-map `u : C → T`, injective because it induces `E → Ω`.
4. For `g ∈ I_Q`, `g` preserves `B` and `T` and is the identity on `L`, so `u` and `g ∘ u`
   induce the same map `K → L`; uniqueness gives `g ∘ u = u`, hence `I_Q ⊆ Aut_E(Ω)`.
5. Conversely, for `g ∈ Aut_E(Ω)` and `b ∈ B`, the rings `C[b]` and `C[g b]` are finite domains
   over the henselian `C`, hence local by the finite-over-henselian-local-product lemma, with
   maximal ideals the preimages of `m_T`; the `C`-isomorphism `g` matches them, so `g Q = Q`.
6. `g` fixes `K` in `L`; by the separable-first lemma and the separably-closed finite-extension
   lemma, `L / K` is purely inseparable, so `g` is the identity on `L` (injective Frobenius in
   characteristic `p`). Hence `I_Q = Aut_E(Ω)`, without any perfection assumption on `κ`.
7. `Ω / F` is Galois (separable-closure Galois lemma); the Galois fixed-field statement gives
   `Ω^{Aut_E(Ω)} = E`, hence `Ω^{I_Q} = E`.
-/
theorem strictLocalInertiaIdentificationRingCore
    (A F K C E Ω : Type u)
    [CommRing A] [IsLocalRing A] [Field F] [Field K] [CommRing C] [Field E] [Field Ω]
    [Algebra A F] [IsFractionRing A F]
    [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [Algebra A C] [Algebra A E] [Algebra C E] [IsFractionRing C E]
    [Algebra F E] [IsScalarTower A C E] [IsScalarTower A F E]
    [Algebra A Ω] [Algebra F Ω] [IsScalarTower A F Ω]
    [SMulCommClass (Ω ≃ₐ[F] Ω) A Ω] [IsSepClosure F Ω]
    (hC : Algebra.IsStrictHenselization A K C)
    (hA : IsDomain A ∧ IsIntegrallyClosed A)
    (hCnormal : IsDomain C ∧ IsIntegrallyClosed C)
    (hAC : Function.Injective (algebraMap A C))
    (Q : Ideal (integralClosure A Ω)) [Q.IsMaximal]
    (hQ : Q.comap (algebraMap A (integralClosure A Ω)) = IsLocalRing.maximalIdeal A) :
    ∃ u : C →ₐ[A] Localization.AtPrime Q,
      ∃ e : E →ₐ[F] Ω,
        e.toRingHom.comp (algebraMap C E) =
          (Ideal.atPrimeToField Q).comp u.toRingHom ∧
        IntermediateField.fixedField (Q.inertia (Ω ≃ₐ[F] Ω)) = e.fieldRange := by
  sorry
