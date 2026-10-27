/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Tensor comparison at an algebra prime and its contraction

Source: Stacks Project, Algebra, Tag 05CL, proof of
`lemma-universally-injective-check-stalks`, the two displayed tensor identities
and the sentence `N_p = N` (blueprint: lem-trf-contracted-prime-tensor-comparison).

The public proposition abbreviation installs the canonical scalar structures inside
its body. Thus the theorem has no local instances or let binders in its signature.
-/

@[expose] public section

universe u v w x y

open scoped TensorProduct

namespace LocalizedModule

/-- The full contracted-prime tensor comparison proposition, using the actual localized
modules and tensor products. The action of `R_p` on `P_q` is restriction along
`Localization.localRingHom`, not additional data. This abbreviation only expands the
statement while keeping its canonical scalar structures available to elaboration.
Source: Stacks Project, Algebra, Tag 05CL, displayed tensor identities and `N_p = N`
(blueprint: lem-trf-contracted-prime-tensor-comparison). -/
noncomputable abbrev ContractedPrimeTensorComparison
    (R : Type u) (A : Type v) (P : Type w) (P' : Type x) (N : Type y)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup P] [AddCommGroup P'] [AddCommGroup N]
    [Module A P] [Module A P'] [Module R P] [Module R P'] [Module R N]
    [IsScalarTower R A P] [IsScalarTower R A P'] (q : PrimeSpectrum A) : Prop :=
  letI := (Localization.localRingHom (q.asIdeal.comap (algebraMap R A))
    q.asIdeal (algebraMap R A) rfl).toAlgebra
  letI : Module (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))
      (LocalizedModule q.asIdeal.primeCompl P) :=
    Module.compHom _ (Localization.localRingHom (q.asIdeal.comap (algebraMap R A))
      q.asIdeal (algebraMap R A) rfl)
  letI : Module (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))
      (LocalizedModule q.asIdeal.primeCompl P') :=
    Module.compHom _ (Localization.localRingHom (q.asIdeal.comap (algebraMap R A))
      q.asIdeal (algebraMap R A) rfl)
  letI := IsScalarTower.of_compHom
    (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))
    (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl P)
  letI := IsScalarTower.of_compHom
    (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))
    (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl P')
  ∃ (α : LocalizedModule q.asIdeal.primeCompl (P ⊗[R] N) ≃ₗ[Localization.AtPrime q.asIdeal]
        (LocalizedModule q.asIdeal.primeCompl P) ⊗[R] N)
    (β : (LocalizedModule q.asIdeal.primeCompl P) ⊗[R] N ≃ₗ[Localization.AtPrime q.asIdeal]
        (LocalizedModule q.asIdeal.primeCompl P) ⊗[
          Localization.AtPrime (q.asIdeal.comap (algebraMap R A))]
          (LocalizedModule (q.asIdeal.comap (algebraMap R A)).primeCompl N))
    (α' : LocalizedModule q.asIdeal.primeCompl (P' ⊗[R] N) ≃ₗ[Localization.AtPrime q.asIdeal]
        (LocalizedModule q.asIdeal.primeCompl P') ⊗[R] N)
    (β' : (LocalizedModule q.asIdeal.primeCompl P') ⊗[R] N ≃ₗ[Localization.AtPrime q.asIdeal]
        (LocalizedModule q.asIdeal.primeCompl P') ⊗[
          Localization.AtPrime (q.asIdeal.comap (algebraMap R A))]
          (LocalizedModule (q.asIdeal.comap (algebraMap R A)).primeCompl N)),
    (∀ (p : P) (n : N) (s : q.asIdeal.primeCompl),
      α (LocalizedModule.mk (p ⊗ₜ[R] n) s) = LocalizedModule.mk p s ⊗ₜ[R] n) ∧
    (∀ (p : P') (n : N) (s : q.asIdeal.primeCompl),
      α' (LocalizedModule.mk (p ⊗ₜ[R] n) s) = LocalizedModule.mk p s ⊗ₜ[R] n) ∧
    (∀ (z : LocalizedModule q.asIdeal.primeCompl P) (n : N),
      β (z ⊗ₜ[R] n) = z ⊗ₜ[
        Localization.AtPrime (q.asIdeal.comap (algebraMap R A))] LocalizedModule.mk n 1) ∧
    (∀ (z : LocalizedModule q.asIdeal.primeCompl P') (n : N),
      β' (z ⊗ₜ[R] n) = z ⊗ₜ[
        Localization.AtPrime (q.asIdeal.comap (algebraMap R A))] LocalizedModule.mk n 1) ∧
    (∀ (f : P →ₗ[A] P') (z : LocalizedModule q.asIdeal.primeCompl (P ⊗[R] N)),
      β' (α' (LocalizedModule.map q.asIdeal.primeCompl
        (TensorProduct.AlgebraTensorModule.rTensor R N f) z)) =
      ((LocalizedModule.map q.asIdeal.primeCompl f).restrictScalars
        (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))).rTensor
        (LocalizedModule (q.asIdeal.comap (algebraMap R A)).primeCompl N) (β (α z))) ∧
    (∀ [Module (Localization.AtPrime (q.asIdeal.comap (algebraMap R A))) N]
        [IsScalarTower R (Localization.AtPrime (q.asIdeal.comap (algebraMap R A))) N],
      ∃ δ : LocalizedModule (q.asIdeal.comap (algebraMap R A)).primeCompl N ≃ₗ[
          Localization.AtPrime (q.asIdeal.comap (algebraMap R A))] N,
        (∀ n : N, δ.symm n = LocalizedModule.mk n 1) ∧
        (∀ (n : N) (t : (q.asIdeal.comap (algebraMap R A)).primeCompl),
          δ (LocalizedModule.mk n t) =
            IsLocalization.mk' (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))
              1 t • n) ∧
        (∀ (f : P →ₗ[A] P') (z : LocalizedModule q.asIdeal.primeCompl (P ⊗[R] N)),
          δ.toLinearMap.lTensor (LocalizedModule q.asIdeal.primeCompl P')
              (β' (α' (LocalizedModule.map q.asIdeal.primeCompl
                (TensorProduct.AlgebraTensorModule.rTensor R N f) z))) =
          ((LocalizedModule.map q.asIdeal.primeCompl f).restrictScalars
            (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))).rTensor N
              (δ.toLinearMap.lTensor (LocalizedModule q.asIdeal.primeCompl P) (β (α z)))))

/-- Canonical tensor comparisons at a prime and its contraction, natural in the algebra module,
including the identification when the base module is already localized.
Source: Stacks Project, Algebra, Tag 05CL, proof of
`lemma-universally-injective-check-stalks`
(blueprint: lem-trf-contracted-prime-tensor-comparison).

Proof:
1. Contract q to p. Elements outside p map outside q, so the fraction formula
   r/t ↦ φ(r)/φ(t) defines `Localization.localRingHom`; restrict the A_q-actions along it.
2. Apply `lem-weil-pbc-localization-tensor-over-base` to P, N and A minus q.
   This gives α with the stated formula. An A-linear map between A_q-modules commutes
   with every denominator and its inverse, and hence is A_q-linear.
3. The identity of P_q is a localization at R minus p: denominators act invertibly,
   the denominator 1 gives surjectivity, and 1 witnesses equality. Apply
   `lem-weil-pbc-localization-tensor-product` to this identity and N → N_p.
4. The resulting β is bijective because denominators already act invertibly on
   P_q tensor_R N: invert them on its first factor. The localization equality
   criterion gives injectivity and the fraction presentation gives surjectivity.
   The pure tensor formula gives A_q-linearity. Repeat for P'.
5. Both naturality composites send (p tensor n)/s to (f(p)/s) tensor (n/1).
   Pure fractions generate the localized tensor module, proving their equality.
6. When N is an R_p-module, δ(n/t) = t⁻¹ n is well defined by the fraction relation:
   cancel the invertible witness and denominators. It is R_p-linear and inverse to
   n ↦ n/1. Tensoring with δ gives the final square, again checked on pure fractions. -/
theorem contractedPrime_tensor_comparison
    (R : Type u) (A : Type v) (P : Type w) (P' : Type x) (N : Type y)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup P] [AddCommGroup P'] [AddCommGroup N]
    [Module A P] [Module A P'] [Module R P] [Module R P'] [Module R N]
    [IsScalarTower R A P] [IsScalarTower R A P'] (q : PrimeSpectrum A) :
    ContractedPrimeTensorComparison R A P P' N q := by
  sorry

end LocalizedModule
