/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Sheaf.Paper.AdicTowerReconstruction
import Sheaf.RingTheory.FiniteModuleComplete
import Sheaf.RingTheory.FiniteOverCompleteRing

/-!
# Adic systems of finite modules over p-adic coefficient rings

Source: Stacks Project, Tags 09B8, 031D, 031B and 00MA;
blueprint `cor-galois-lisse-representations`, steps 6, 7, 9 and 10
(blueprint: lem-pod-adic-limit-finite-modules).

Indices `n : ℕ` denote the positive exponent `n + 1`. A module over the coefficient
quotient is represented by its underlying module over the valuation ring, annihilated
by the corresponding ideal. Surjectivity and the specified kernel say that the
transition induces the required quotient isomorphism.
-/

@[expose] public section

universe u v w z

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace Padic

/-- Reconstruction of an adic system of finite coefficient modules.

Source: Stacks Tags 09B8 and 031D (blueprint: lem-pod-adic-limit-finite-modules), part 1.
Proof: apply lem-pod-adic-tower-reconstruction to the principal uniformizer ideal.
The sections submodule is the inverse limit. Its projections are surjective with
kernel the indicated ideal power, and identify its product-subspace topology with
its maximal-ideal-adic topology. By lem-weil-l-adic-extension-complete the coefficient
field is complete; its closed unit ball is complete too. The limit is separated and
its first reduction is finite, so lem-weil-pbc-finite-over-complete-ring (031D) makes
it finitely generated. Surjectivity and the kernel equality give the canonical
quotient isomorphisms by the first isomorphism theorem. -/
theorem adicLimit_finite_modules (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    let R := coefficientExtensionIntegers l E
    let I := Ideal.span ({coefficientExtensionUniformizer l E} : Set R)
    ∀ (F : ℕᵒᵖ ⥤ ModuleCat.{v} R),
      (∀ n : ℕ, Module.Finite R (F.obj (op n))) →
      (∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (F.obj (op n))) = ⊥) →
      (∀ n : ℕ,
        Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom ∧
        LinearMap.ker (F.map (homOfLE (Nat.le_succ n)).op).hom =
          I ^ (n + 1) • (⊤ : Submodule R (F.obj (op (n + 1))))) →
      let S := ModuleCat.sectionsSubmodule F
      Module.Finite R S ∧
        (∀ n : ℕ,
          let p := (LinearMap.proj (op n)).comp S.subtype
          Function.Surjective p ∧ LinearMap.ker p = I ^ (n + 1) • (⊤ : Submodule R S)) ∧
        (letI : ∀ j : ℕᵒᵖ, TopologicalSpace (F.obj j) := fun _ ↦ ⊥
         TopologicalSpace.induced (fun x : S ↦ x.val) inferInstance =
           (coefficientExtensionMaximalIdeal l E).adicModuleTopology S) := by
  sorry

/-- Completeness, quotient towers, and Hom comparison for finite integral modules.

Source: Stacks Tags 031B, 09B8 and 00MA
(blueprint: lem-pod-adic-limit-finite-modules), part 2.
Proof: the valuation ring is Noetherian since it is a DVR and complete by
lem-weil-l-adic-extension-complete and the closed-unit-ball argument above.
Apply lem-weil-pbc-finite-module-complete-over-complete-noetherian to any finite
module. The canonical quotient transitions are surjective, with the stated kernels,
and the quotients are finite coefficient modules. A linear map preserves every ideal
power times the module and hence is continuous. Its reductions are compatible.
For a compatible family of reductions, send an element to the family of its images
in the target quotients, then use completeness of the target to reconstruct the
unique linear map. Separatedness gives uniqueness. The final unique-existence
clause is precisely bijectivity of the reduction map to the inverse limit of Hom. -/
theorem finite_module_adic_complete_and_hom (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    let R := coefficientExtensionIntegers l E
    let I := Ideal.span ({coefficientExtensionUniformizer l E} : Set R)
    let J := coefficientExtensionMaximalIdeal l E
    (∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
      IsAdicComplete J M ∧ Function.Bijective (AdicCompletion.of I M) ∧
        (∀ n : ℕ,
          Module.Finite (R ⧸ I ^ (n + 1)) (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) ∧
          let t := Submodule.factorPow I M (Nat.le_succ (n + 1))
          Function.Surjective t ∧ LinearMap.ker t =
            I ^ (n + 1) • (⊤ : Submodule R (M ⧸ (I ^ (n + 2) • ⊤ : Submodule R M))))) ∧
    (∀ (M : Type v) (N : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M]
      [AddCommGroup N] [Module R N] [Module.Finite R N],
      (∀ f : M →ₗ[R] N, @Continuous M N (J.adicModuleTopology M)
        (J.adicModuleTopology N) f) ∧
      (∀ g : ∀ n : ℕ,
        (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) →ₗ[R ⧸ I ^ (n + 1)]
          (N ⧸ (I ^ (n + 1) • ⊤ : Submodule R N)),
        (∀ n : ℕ,
          (Submodule.factorPow I N (Nat.le_succ (n + 1))).comp
            ((g (n + 1)).restrictScalars R) =
          ((g n).restrictScalars R).comp
            (Submodule.factorPow I M (Nat.le_succ (n + 1)))) →
        ∃! f : M →ₗ[R] N, ∀ n : ℕ, f.reduceModIdeal (I ^ (n + 1)) = g n)) := by
  sorry

/-- Tensor products commute with positive coefficient reductions, as a compatible family.

Source: right exactness of tensor products, Stacks Tag 00MA
(blueprint: lem-pod-adic-limit-finite-modules), part 3, first identity.
Proof: reduce both tensor factors modulo the uniformizer power. Right exactness
identifies the quotient of their tensor product with the tensor of the two quotients
over the coefficient ring. The equivalence sends the class of a pure tensor to the
tensor of its classes. The reduction maps on pure tensors define the maps `t` below;
their formula shows commutativity for every pair of levels. This is step 5 of the
node's proof. -/
theorem finite_module_tensor_reductions (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    let R := coefficientExtensionIntegers l E
    let I := Ideal.span ({coefficientExtensionUniformizer l E} : Set R)
    ∀ (M : Type v) (N : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M]
      [AddCommGroup N] [Module R N] [Module.Finite R N],
      ∃ e : ∀ n : ℕ,
        ((M ⊗[R] N) ⧸ (I ^ (n + 1) • ⊤ : Submodule R (M ⊗[R] N))) ≃ₗ[R ⧸ I ^ (n + 1)]
          ((M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) ⊗[R ⧸ I ^ (n + 1)]
            (N ⧸ (I ^ (n + 1) • ⊤ : Submodule R N))),
        (∀ (n : ℕ) (x : M) (y : N),
          e n (Submodule.Quotient.mk (x ⊗ₜ[R] y)) =
            Submodule.Quotient.mk x ⊗ₜ[R ⧸ I ^ (n + 1)] Submodule.Quotient.mk y) ∧
        (∀ (m n : ℕ) (h : m ≤ n),
          ∃ t :
            ((M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) ⊗[R ⧸ I ^ (n + 1)]
              (N ⧸ (I ^ (n + 1) • ⊤ : Submodule R N))) →ₗ[R]
            ((M ⧸ (I ^ (m + 1) • ⊤ : Submodule R M)) ⊗[R ⧸ I ^ (m + 1)]
              (N ⧸ (I ^ (m + 1) • ⊤ : Submodule R N))),
            (∀ (x : M) (y : N),
              t (Submodule.Quotient.mk x ⊗ₜ[R ⧸ I ^ (n + 1)] Submodule.Quotient.mk y) =
                Submodule.Quotient.mk x ⊗ₜ[R ⧸ I ^ (m + 1)] Submodule.Quotient.mk y) ∧
            t.comp ((e n).toLinearMap.restrictScalars R) =
              ((e m).toLinearMap.restrictScalars R).comp
                (Submodule.factorPow I (M ⊗[R] N) (Nat.add_le_add_right h 1))) := by
  sorry

/-- Scalar extension commutes with coefficient reductions, as a compatible family.

Source: right exactness of tensor products, Stacks Tag 00MA
(blueprint: lem-pod-adic-limit-finite-modules), part 3, second identity.
Here `α` is the restriction of the field embedding to the two rings of integers;
its displayed compatibility specifies that restriction, rather than an arbitrary
scalar action. Powers are those of the original uniformizer, including in `𝒪_L`.
Proof: the extended absolute value restricts to that of `E`, so the field embedding
restricts to the ring homomorphism `α`. Apply the right-exact tensor argument to `M` and
`𝒪_L`. The pure-tensor formula gives the quotient isomorphism and its compatibility
with all level reductions. This is step 6 of the node's proof. -/
theorem finite_extension_scalar_reductions (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type z) [Field L] [Algebra E L] [FiniteDimensional E L]
    [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsScalarTower ℚ_[l] E L] :
    let R := coefficientExtensionIntegers l E
    let S := coefficientExtensionIntegers l L
    let I := Ideal.span ({coefficientExtensionUniformizer l E} : Set R)
    ∃ α : R →+* S, (∀ r : R, (α r : L) = algebraMap E L (r : E)) ∧
      letI : Algebra R S := α.toAlgebra
      ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
      ∃ e : ∀ n : ℕ,
        ((M ⊗[R] S) ⧸ (I ^ (n + 1) • ⊤ : Submodule R (M ⊗[R] S))) ≃ₗ[R ⧸ I ^ (n + 1)]
          ((M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) ⊗[R ⧸ I ^ (n + 1)]
            (S ⧸ (I ^ (n + 1) • ⊤ : Submodule R S))),
        (∀ (n : ℕ) (x : M) (y : S),
          e n (Submodule.Quotient.mk (x ⊗ₜ[R] y)) =
            Submodule.Quotient.mk x ⊗ₜ[R ⧸ I ^ (n + 1)] Submodule.Quotient.mk y) ∧
        (∀ (m n : ℕ) (h : m ≤ n),
          ∃ t :
            ((M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) ⊗[R ⧸ I ^ (n + 1)]
              (S ⧸ (I ^ (n + 1) • ⊤ : Submodule R S))) →ₗ[R]
            ((M ⧸ (I ^ (m + 1) • ⊤ : Submodule R M)) ⊗[R ⧸ I ^ (m + 1)]
              (S ⧸ (I ^ (m + 1) • ⊤ : Submodule R S))),
            (∀ (x : M) (y : S),
              t (Submodule.Quotient.mk x ⊗ₜ[R ⧸ I ^ (n + 1)] Submodule.Quotient.mk y) =
                Submodule.Quotient.mk x ⊗ₜ[R ⧸ I ^ (m + 1)] Submodule.Quotient.mk y) ∧
            t.comp ((e n).toLinearMap.restrictScalars R) =
              ((e m).toLinearMap.restrictScalars R).comp
                (Submodule.factorPow I (M ⊗[R] S) (Nat.add_le_add_right h 1))) := by
  sorry

end Padic
