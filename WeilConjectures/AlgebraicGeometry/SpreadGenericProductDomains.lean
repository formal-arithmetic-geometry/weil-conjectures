/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Spec

import WeilConjectures.AlgebraicGeometry.SpreadGenericProductEmbedding
import WeilConjectures.RingTheory.FiniteProductFieldImageFactors

/-!
# Spreading the generic product idempotents
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct
open AlgebraicGeometry

/-- A specified generic product of fields spreads to a product of finite domains, after
shrinking a specified finite etale model of its base field. This is only the algebraic
idempotent-spreading step: no radicial or universal-homeomorphism conclusion is asserted. -/
theorem exists_spread_generic_product_domains
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A]
    (B : Type v) [CommRing B] [Algebra A B] [Module.Finite A B]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (K' : Type (max u v)) [Field K'] [Algebra K K'] [Algebra A K']
    [IsScalarTower A K K']
    (r : ℕ) (L : Fin r → Type (max u v)) [∀ j, Field (L j)]
    [∀ j, Algebra K' (L j)]
    (hsplit :
      letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := K ⊗[A] B) (B := K')
      Nonempty ((((K ⊗[A] B) ⊗[K] K') ⧸
        nilradical ((K ⊗[A] B) ⊗[K] K')) ≃ₐ[K'] (∀ j, L j)))
    (c0 : A) (hc0 : c0 ≠ 0) (S0 : Subalgebra A K')
    [IsLocalization.Away c0 S0] (A0 : Subalgebra S0 K')
    [Module.Finite S0 A0] [Algebra.Etale S0 A0] [IsFractionRing A0 K']
    (hsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap S0 A0)))) :
    ∃ (c : A) (A' : Type u) (_ : CommRing A') (_ : Algebra (Localization.Away c) A')
      (_ : Algebra A A') (_ : IsScalarTower A (Localization.Away c) A')
      (_ : IsDomain A') (_ : Algebra A' K'),
      c ≠ 0 ∧ Module.Finite (Localization.Away c) A' ∧
        Algebra.Etale (Localization.Away c) A' ∧ IsFractionRing A' K' ∧
        Surjective (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away c) A'))) ∧
        ∃ (D : Fin r → Type u) (_ : ∀ j, CommRing (D j))
          (_ : ∀ j, Algebra A' (D j)) (_ : ∀ j, Algebra (D j) (L j))
          (_ : ∀ j, Algebra A' (L j))
          (_ : ∀ j, IsScalarTower A' (D j) (L j))
          (_ : ∀ j, IsScalarTower A' K' (L j)),
          (∀ j, Module.Finite A' (D j) ∧ IsDomain (D j) ∧ IsFractionRing (D j) (L j)) ∧
          letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := A')
          Nonempty (((B ⊗[A] A') ⧸ nilradical (B ⊗[A] A')) ≃ₐ[A'] (∀ j, D j)) := by
  obtain ⟨c, A', instRing, instLocAlg, instAlg, instTower, instDomain, instFieldAlg,
    hc, hfinite, hetale, hfrac, hsurj', instFactors, instFactorTowers, f, hf, hid, hden⟩ :=
    exists_spread_generic_product_embedding A B K K' r L hsplit c0 hc0 S0 A0 hsurj
  let := instRing
  let := instLocAlg
  let := instAlg
  let := instTower
  let := instDomain
  let := instFieldAlg
  let := hfrac
  let := instFactors
  let := instFactorTowers
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := A')
  have : Module.Finite A' (B ⊗[A] A') :=
    Module.Finite.equiv (Algebra.TensorProduct.commRight A A' B).toLinearEquiv
  have hbase (j : Fin r) : Function.Injective (algebraMap A' (L j)) := by
    rw [IsScalarTower.algebraMap_eq A' K' (L j)]
    exact (RingHom.injective (algebraMap K' (L j))).comp (IsFractionRing.injective A' K')
  obtain ⟨D, instDRing, instDAlg, instDLAlg, instDLTower, hD, hequiv⟩ :=
    exists_finite_domain_factors_of_product_embedding A'
      ((B ⊗[A] A') ⧸ nilradical (B ⊗[A] A')) r L hbase f hf hid hden
  exact ⟨c, A', instRing, instLocAlg, instAlg, instTower, instDomain, instFieldAlg,
    hc, hfinite, hetale, hfrac, hsurj', D, instDRing, instDAlg, instDLAlg,
    instFactors, instDLTower, instFactorTowers, hD, hequiv⟩
