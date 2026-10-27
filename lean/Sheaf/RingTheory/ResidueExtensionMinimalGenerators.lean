/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q12
-/
module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! # Minimal generators and extension of the residue field

Source: Stacks Project, Tags 00SI and 00SJ, residue-fibre dimensions and Nakayama;
Tag 00DV, parts (4) and (8).
(blueprint: lem-weil-pbc-residue-extension-minimal-generators)

The scoped instances construct the composite residue-field action and transport the
scalar action through tensor symmetry. In particular all tensors below retain the
factor order used in the source node.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace IsLocalRing

namespace ResidueGeneratorCount

/-- The actual residue quotient, with its existing quotient vector-space structure.
Source: Stacks Project, Tags 00SI and 00DV.
(blueprint: lem-weil-pbc-residue-extension-minimal-generators) -/
abbrev quotient (A : Type u) [CommRing A] [IsLocalRing A]
    (M : Type v) [AddCommGroup M] [Module A M] :=
  M ⧸ (maximalIdeal A • (⊤ : Submodule A M))

/-- The existing quotient action, exposed through Mathlib's named residue field.
Source: Stacks Project, Tags 00SI and 00DV.
(blueprint: lem-weil-pbc-residue-extension-minimal-generators) -/
@[instance_reducible] def quotientResidueModule
    (A : Type u) [CommRing A] [IsLocalRing A]
    (M : Type v) [AddCommGroup M] [Module A M] :
    Module (ResidueField A) (quotient A M) :=
  inferInstanceAs (Module (A ⧸ maximalIdeal A)
    (M ⧸ (maximalIdeal A • (⊤ : Submodule A M))))

/-- The composite action of the local ring on an extension of its residue field.
Source: Stacks Project, Tag 00SI, displayed residue-field tensors.
(blueprint: lem-weil-pbc-residue-extension-minimal-generators) -/
@[instance_reducible] noncomputable def residueAlgebra
    (A : Type u) [CommRing A] [IsLocalRing A]
    (L : Type w) [Field L] [Algebra (ResidueField A) L] : Algebra A L :=
  ((algebraMap (ResidueField A) L).comp (residue A)).toAlgebra

/-- The scalar action on a tensor whose scalar-extension factor is on the right.
It is transported through the existing tensor symmetry, and has actual data.
Source: Stacks Project, Tag 00SI, displayed residue-field tensors.
(blueprint: lem-weil-pbc-residue-extension-minimal-generators) -/
@[instance_reducible] noncomputable def rightTensorModule
    (R : Type u) [CommRing R] (N : Type v) [AddCommGroup N] [Module R N]
    (S : Type w) [CommRing S] [Algebra R S] : Module S (N ⊗[R] S) :=
  (TensorProduct.comm R N S).toAddEquiv.module S

attribute [scoped instance] quotientResidueModule
attribute [scoped instance 90] residueAlgebra rightTensorModule

end ResidueGeneratorCount

open ResidueGeneratorCount
open scoped ResidueGeneratorCount

variable (A : Type u) [CommRing A] [IsLocalRing A]
variable (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
variable (L : Type w) [Field L] [Algebra (ResidueField A) L]

/-- Minimal generators are the residue dimension, unchanged by any residue-field extension.
Source: Stacks Project, Tags 00SI and 00SJ, residue-fibre dimension argument;
Tag 00DV, parts (4) and (8).
(blueprint: lem-weil-pbc-residue-extension-minimal-generators)

Proof plan:
1. Reduce a finite generating list modulo the maximal ideal. Its images span the
   quotient. Delete dependent vectors successively to obtain a finite basis; its
   length is the finrank, and every spanning list has at least that length
   (def-weil-finite-dimensional-subspace, def-weil-vector-space-dimension).
2. Lift any residue basis. Nakayama says every such lift generates the finite
   module (lem-weil-pbc-nakayama-local-generators); this includes the empty basis.
3. A generating r-tuple reduces to a spanning r-tuple. Conversely pad the lifted
   basis with zeroes to reach any larger length. This gives all bounds and the
   least generator count, including zero.
4. Base change of a basis gives the basis v_i tensor 1, without any condition on
   the field extension (lem-weil-pbc-free-module-base-change-free,
   def-weil-pbc-free-module, def-weil-pbc-module-tensor-product). Its length gives
   finiteness and equality of both dimensions.
5. Apply lem-weil-pbc-tensor-over-quotient-ring and tensor symmetry. The canonical
   maps send m tensor a to a times the residue of m and m tensor l to the residue
   of m tensor l. Their inverses lift residue classes; maximal-ideal multiples
   vanish in the tensors. These maps preserve the marked vectors, so all bounds,
   basis statements, and dimension statements transport to the two fibres. -/
theorem residue_extension_minimal_generators :
    FiniteDimensional (ResidueField A) (quotient A M) ∧
    FiniteDimensional L ((quotient A M) ⊗[ResidueField A] L) ∧
    FiniteDimensional (ResidueField A) (M ⊗[A] (ResidueField A)) ∧
    FiniteDimensional L (M ⊗[A] L) ∧
    (∀ r : ℕ,
      ((∃ x : Fin r → M, Submodule.span A (Set.range x) = ⊤) ↔
        Module.finrank (ResidueField A) (quotient A M) ≤ r) ∧
      (Module.finrank (ResidueField A) (quotient A M) ≤ r ↔
        Module.finrank L ((quotient A M) ⊗[ResidueField A] L) ≤ r) ∧
      ((∃ x : Fin r → M, Submodule.span A (Set.range x) = ⊤) ↔
        Module.finrank (ResidueField A) (M ⊗[A] (ResidueField A)) ≤ r) ∧
      ((∃ x : Fin r → M, Submodule.span A (Set.range x) = ⊤) ↔
        Module.finrank L (M ⊗[A] L) ≤ r)) ∧
    IsLeast {r : ℕ | ∃ x : Fin r → M, Submodule.span A (Set.range x) = ⊤}
      (Module.finrank (ResidueField A) (quotient A M)) ∧
    Module.finrank (ResidueField A) (quotient A M) =
      Module.finrank L ((quotient A M) ⊗[ResidueField A] L) ∧
    Module.finrank (ResidueField A) (M ⊗[A] (ResidueField A)) =
      Module.finrank (ResidueField A) (quotient A M) ∧
    Module.finrank L (M ⊗[A] L) =
      Module.finrank L ((quotient A M) ⊗[ResidueField A] L) ∧
    (∀ (d : ℕ) (b : Module.Basis (Fin d) (ResidueField A) (quotient A M)),
      (∀ x : Fin d → M,
        (∀ i, Submodule.Quotient.mk (x i) = b i) →
        Submodule.span A (Set.range x) = ⊤) ∧
      (∃ c : Module.Basis (Fin d) L ((quotient A M) ⊗[ResidueField A] L),
        ∀ i, c i = b i ⊗ₜ[ResidueField A] (1 : L)) ∧
      (∀ r : ℕ, r < d →
        ¬ ∃ x : Fin r → M, Submodule.span A (Set.range x) = ⊤)) ∧
    (∀ (d : ℕ)
      (b : Module.Basis (Fin d) (ResidueField A) (M ⊗[A] (ResidueField A))),
      (∀ x : Fin d → M,
        (∀ i, x i ⊗ₜ[A] (1 : ResidueField A) = b i) →
        Submodule.span A (Set.range x) = ⊤) ∧
      (∀ x : Fin d → M,
        (∀ i, x i ⊗ₜ[A] (1 : ResidueField A) = b i) →
        ∃ c : Module.Basis (Fin d) L (M ⊗[A] L),
          ∀ i, c i = x i ⊗ₜ[A] (1 : L)) ∧
      (∀ r : ℕ, r < d →
        ¬ ∃ x : Fin r → M, Submodule.span A (Set.range x) = ⊤)) ∧
    (∃ e : (M ⊗[A] (ResidueField A)) ≃ₗ[ResidueField A] quotient A M,
      ∀ (m : M) (a : ResidueField A),
        e (m ⊗ₜ[A] a) = a • Submodule.Quotient.mk m) ∧
    (∃ e : (M ⊗[A] L) ≃ₗ[L] ((quotient A M) ⊗[ResidueField A] L),
      ∀ (m : M) (l : L), e (m ⊗ₜ[A] l) = Submodule.Quotient.mk m ⊗ₜ l) := by
  sorry

end IsLocalRing
