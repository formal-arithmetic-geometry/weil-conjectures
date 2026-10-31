/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FreeModule.Basic
import WeilConjectures.AlgebraicGeometry.SeparableResidueCotangentInjective

/-!
# Differentials of uniformizers with finite separable residue field

Source: Stacks Project, Curves, Tag 0C1E, `lemma-uniformizer-works`, and Algebra,
Tag 00TU, `lemma-computation-differential`
(blueprint: lem-a1-dvr-separable-residue-differential-basis).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace IsDiscreteValuationRing

/-- In a Noetherian DVR over a field with finite separable residue field and free
rank-one differentials, every uniformizer has nonzero cotangent class and nonzero
residue differential. Its coefficient in every rank-one basis is a unit, and
multiplication by its differential is a linear equivalence with the stated inverse.

Source: Stacks Project, Curves, Tag 0C1E, `lemma-uniformizer-works`, middle and final
proof sentences; Algebra, Tag 00TU, `lemma-computation-differential`
(blueprint: lem-a1-dvr-separable-residue-differential-basis).

Proof:
1. The maximal ideal is nonzero in a DVR, so its generator t is nonzero. If t lay in
   its square, the equality m = tA would give t = t²b. Cancellation would imply
   1 = tb in m, a contradiction. Thus the class of t in m/m² is nonzero.
2. A finite residue extension is finitely generated as a field. Algebraic
   separability implies separability in the sense of separably generated finitely
   generated subextensions: every such subextension has empty transcendence basis
   and is separable algebraic, since its minimal polynomials agree with those in κ.
3. Apply Algebra.separable_residue_cotangent_injective to the nonzero class of t.
   The canonical cotangent map sends this class to dt tensor 1, which is nonzero.
4. In any rank-one basis e, write dt = a e uniquely. If a were in m, tensor
   balancing would give dt tensor 1 = e tensor the residue of a = 0. Thus a is
   outside m, hence is a unit of the local ring.
5. The map b ↦ b dt = ba e is A-linear. The inverse sends c e to c a⁻¹.
   Unique coordinates make this inverse well defined and linear; the two
   composites are identities by aa⁻¹ = a⁻¹a = 1. -/
theorem separable_residue_differential_basis
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsNoetherianRing A] [Algebra k A]
    [Module.Finite k (IsLocalRing.ResidueField A)]
    [Algebra.IsSeparable k (IsLocalRing.ResidueField A)]
    (hfree : Nonempty (Module.Basis (Fin 1) A (KaehlerDifferential k A)))
    (t : A) (ht : IsLocalRing.maximalIdeal A = Ideal.span {t}) :
    (∃ htmem : t ∈ IsLocalRing.maximalIdeal A,
      (IsLocalRing.maximalIdeal A).toCotangent ⟨t, htmem⟩ ≠ 0) ∧
    (KaehlerDifferential.D k A t) ⊗ₜ[A] (1 : IsLocalRing.ResidueField A) ≠ 0 ∧
    ∀ e : Module.Basis (Fin 1) A (KaehlerDifferential k A), ∃ a : A,
      (KaehlerDifferential.D k A t = a • e 0 ∧
        ∀ a' : A, KaehlerDifferential.D k A t = a' • e 0 → a' = a) ∧
      IsUnit a ∧ ∃ φ : A ≃ₗ[A] KaehlerDifferential k A,
        (∀ b : A, φ b = b • KaehlerDifferential.D k A t) ∧
        ∀ c : A, φ.symm (c • e 0) = c * Ring.inverse a := by
  sorry

end IsDiscreteValuationRing
