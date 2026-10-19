/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q96
-/
module

public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes

/-!
# Associated primes of a fibre module and its fibre ring

Source: Stacks Project, Algebra, Remark Tag 05E0 (remark-bourbaki), through
Lemmas Tags 05BY and 05BZ (blueprint: lem-trf-fibre-associated-primes-module-ring).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace RingTheory

/-- The canonical map `b ↦ b ⊗ 1` from the first factor `B` of the source-oriented fibre
tensor product `B ⊗[A] κ(p)`.
Source: Stacks Project, Algebra, Remark Tag 05E0 (remark-bourbaki), with the fibre map
of Lemma Tag 05BZ (blueprint: lem-trf-fibre-associated-primes-module-ring). -/
noncomputable def fibreRingMap (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] : B →+* B ⊗[A] p.ResidueField :=
  (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] p.ResidueField).toRingHom

/-- Contraction identifies the element-annihilator associated primes of a fibre module
with those of the fibre ring viewed by restriction of scalars.
Source: Stacks Project, Algebra, Remark Tag 05E0 (remark-bourbaki), through Lemmas
Tags 05BY and 05BZ; the common-denominator argument is expanded in the node proof.
(blueprint: lem-trf-fibre-associated-primes-module-ring)

Proof: represent every tensor as a localized image of an element of `B`; compute the
annihilator and its contraction elementwise; use primality in both directions; then
restrict the fibre-ring prime correspondence to the annihilator-defined associated
primes. No flatness or Noetherian hypothesis is used. -/
theorem fibre_associated_primes_module_ring
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (L : Type w) [AddCommGroup L]
    [Module (B ⊗[A] p.ResidueField) L] :
    Set.BijOn
        (Ideal.comap (fibreRingMap A B p))
        (annihilatorAssociatedPrimes (B ⊗[A] p.ResidueField) L)
        (@annihilatorAssociatedPrimes B _ L _
          (Module.compHom L (fibreRingMap A B p))) ∧
      (∀ z : L,
        Ideal.comap (fibreRingMap A B p)
            (@Submodule.colon (B ⊗[A] p.ResidueField) L _ _ inferInstance
              (⊥ : @Submodule (B ⊗[A] p.ResidueField) L _ _ inferInstance) {z}) =
          @Submodule.colon B L _ _ (Module.compHom L (fibreRingMap A B p))
            (⊥ : @Submodule B L _ _ (Module.compHom L (fibreRingMap A B p))) {z} ∧
        @Submodule.colon (B ⊗[A] p.ResidueField) L _ _ inferInstance
            (⊥ : @Submodule (B ⊗[A] p.ResidueField) L _ _ inferInstance) {z} =
          Ideal.map (fibreRingMap A B p)
            (@Submodule.colon B L _ _ (Module.compHom L (fibreRingMap A B p))
              (⊥ : @Submodule B L _ _ (Module.compHom L (fibreRingMap A B p))) {z}) ∧
        ((@Submodule.colon (B ⊗[A] p.ResidueField) L _ _ inferInstance
              (⊥ : @Submodule (B ⊗[A] p.ResidueField) L _ _ inferInstance) {z}).IsPrime ↔
          (@Submodule.colon B L _ _ (Module.compHom L (fibreRingMap A B p))
            (⊥ : @Submodule B L _ _ (Module.compHom L (fibreRingMap A B p))) {z}).IsPrime)) ∧
      (∀ q : Ideal B,
        q ∈ @annihilatorAssociatedPrimes B _ L _
          (Module.compHom L (fibreRingMap A B p)) →
          q.comap (algebraMap A B) = p) := by
  sorry

end RingTheory
