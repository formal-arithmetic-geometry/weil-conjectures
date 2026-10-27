module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.FixedSubmodule
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas

/-! # The Frobenius projection on symmetric invariant tensors

Source: Milne, Algebraic Groups (2017), Section 11(i), printed p. 224, the diagram
preceding Definition 11.39 (blueprint: lem-sfb-symmetric-invariant-frobenius-projection).

## Main definitions

* `SymmetricInvariantFrobenius.projectionForBasis`: the finite diagonal-coordinate map.
* `SymmetricInvariantFrobenius.projection`: its chosen-basis realization.
* `SymmetricInvariantFrobenius.twistMap`: the Frobenius base change of a linear map.
* `SymmetricInvariantFrobenius.tensorComparison`: the canonical tensor comparison.

## Main statements

* `SymmetricInvariantFrobenius.symmetric_invariant_frobenius_projection`: the orbit basis,
  basis independence, naturality, tensor compatibility and unit normalization.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w j

open TensorProduct CategoryTheory
open scoped ChangeOfRings

namespace SymmetricInvariantFrobenius

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The diagonal-coordinate projection for a basis, extended to the full tensor power.
Only its restriction to permutation-invariant tensors is intrinsic.
Source: Milne, Section 11(i), p. 224, diagram before Definition 11.39
(blueprint: lem-sfb-symmetric-invariant-frobenius-projection). -/
noncomputable def projectionForBasis {M : Type v} [AddCommGroup M] [Module k M]
    {J : Type j} (B : Module.Basis J k M) :
    (⨂[k] (_ : Fin p), M) →ₗ[k]
      (ModuleCat.extendScalars (frobenius k p)).obj (ModuleCat.of k M) := by
  classical
  exact (Finsupp.linearCombination k (M :=
    (ModuleCat.extendScalars (frobenius k p)).obj (ModuleCat.of k M))
    (fun t : Fin p → J ↦
    if ∀ i, t i = t ⟨0, (Fact.out : p.Prime).pos⟩ then
      @TensorProduct.tmul k _ k M _ _ (Module.compHom k (frobenius k p)) _
        1 (B (t ⟨0, (Fact.out : p.Prime).pos⟩)) else 0)).comp
        (Basis.piTensorProduct (fun _ : Fin p ↦ B)).repr.toLinearMap

/-- Base change of a linear map along Frobenius, sending c tensor m to c tensor h(m).
Source: Milne, Section 11(i), p. 224, diagram before Definition 11.39
(blueprint: lem-sfb-symmetric-invariant-frobenius-projection). -/
noncomputable def twistMap {M : Type v} {N : Type w}
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] (h : M →ₗ[k] N) :
    (ModuleCat.extendScalars (frobenius k p)).obj (ModuleCat.of k M) →ₗ[k]
      (ModuleCat.extendScalars (frobenius k p)).obj (ModuleCat.of k N) := by
  letI : Algebra k k := (frobenius k p).toAlgebra
  exact LinearMap.baseChange k h

/-- The canonical comparison from the tensor product of two Frobenius base changes
onto the base change of their tensor product.
Source: Milne, Section 11(i), p. 224, diagram before Definition 11.39
(blueprint: lem-sfb-symmetric-invariant-frobenius-projection). -/
noncomputable def tensorComparison (M : Type v) (N : Type w)
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] :
    ((ModuleCat.extendScalars (frobenius k p)).obj (ModuleCat.of k M) ⊗[k]
      (ModuleCat.extendScalars (frobenius k p)).obj (ModuleCat.of k N)) ≃ₗ[k]
      (ModuleCat.extendScalars (frobenius k p)).obj (ModuleCat.of k (M ⊗[k] N)) := by
  letI : Algebra k k := (frobenius k p).toAlgebra
  exact (TensorProduct.AlgebraTensorModule.distribBaseChange k k M N).symm

/-- The concrete projection using the chosen vector-space basis; the theorem asserts
that its restriction to invariants is independent of that choice.
Source: Milne, Section 11(i), p. 224, diagram before Definition 11.39
(blueprint: lem-sfb-symmetric-invariant-frobenius-projection). -/
noncomputable def projection (M : Type v) [AddCommGroup M] [Module k M] :
    (⨂[k] (_ : Fin p), M) →ₗ[k]
      (ModuleCat.extendScalars (frobenius k p)).obj (ModuleCat.of k M) :=
  projectionForBasis k p (Module.Basis.ofVectorSpace k M)

open Classical in
/-- The orbit basis, basis independence, functoriality, tensor compatibility and unit
normalization of the invariant-tensor Frobenius projection.
Source: Milne, Section 11(i), printed p. 224, diagram before Definition 11.39
(blueprint: lem-sfb-symmetric-invariant-frobenius-projection).

Proof plan: choose bases using lem-weil-pbc-vector-space-free. By
lem-sfb-finite-tensor-product-basis-coordinates, tensor words form a basis, including
for infinite bases. Invariance means coefficients are constant on permutation orbits;
finite support gives the asserted orbit-sum basis. Singleton orbits are constant words.
For a nonconstant word choose a letter occurring r times with 0 < r < p. Counting
pairs of a word and a position occupied by that letter gives r times the orbit size
as p times an integer. Primality implies p divides the orbit size, so it is zero in k.
The base-changed basis of lem-weil-pbc-free-module-base-change-free and the balancing
rule of def-weil-module-base-change identify the diagonal-coordinate map with the
specified projection. Frobenius is the ring map of def-weil-ring-frobenius.
For a linear map with matrix entries h_ji, the coefficient of a constant output word
in the image of an orbit sum is its orbit size times the product of the corresponding
matrix entries. It vanishes on nonconstant orbits, and on a constant input word it
is h_ji^p. This is precisely base change along Frobenius, proving naturality.
Apply that calculation to the identity with two different bases to prove basis
independence. Tensor universality from def-weil-pbc-module-tensor-product gives
interleaving; it commutes with simultaneous permutations. Its constant paired-word
coefficient is the product of the two constant-word coefficients. The canonical
base-change tensor comparison sends (a tensor m) tensor (b tensor n) to
ab tensor (m tensor n), so both sides of tensor compatibility have identical finite
coordinate expansions. Finally use the basis {1} of k; its projection is 1 tensor 1,
and the unit isomorphism sends this to 1. No division by an orbit size is used. -/
theorem symmetric_invariant_frobenius_projection
    (M : Type v) (N : Type w) [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] :
    (∀ (J : Type j) (B : Module.Basis J k M),
      ∃ OB : Module.Basis
        (Set.range (fun t : Fin p → J ↦
          Finset.univ.image (fun e : Equiv.Perm (Fin p) ↦ t ∘ e))) k
        (↥(⨅ e : Equiv.Perm (Fin p),
          ((PiTensorProduct.reindex k (fun _ : Fin p ↦ M) e).toLinearMap).fixedSubmodule)),
        ∀ t, (OB ⟨Finset.univ.image (fun e : Equiv.Perm (Fin p) ↦ t ∘ e),
          Set.mem_range_self t⟩).val =
          ∑ s ∈ Finset.univ.image (fun e : Equiv.Perm (Fin p) ↦ t ∘ e),
            PiTensorProduct.tprod k (fun i ↦ B (s i))) ∧
    (∀ (J : Type j) (B : Module.Basis J k M) (t : Fin p → J),
      ((∀ i, t i = t ⟨0, (Fact.out : p.Prime).pos⟩) →
        projectionForBasis k p B
          (∑ s ∈ Finset.univ.image (fun e : Equiv.Perm (Fin p) ↦ t ∘ e),
            PiTensorProduct.tprod k (fun i ↦ B (s i))) =
          (1 : k) ⊗ₜ[k, frobenius k p] B (t ⟨0, (Fact.out : p.Prime).pos⟩)) ∧
      ((¬ ∀ i, t i = t ⟨0, (Fact.out : p.Prime).pos⟩) →
        projectionForBasis k p B
          (∑ s ∈ Finset.univ.image (fun e : Equiv.Perm (Fin p) ↦ t ∘ e),
            PiTensorProduct.tprod k (fun i ↦ B (s i))) = 0)) ∧
    (∀ (J : Type j) (B : Module.Basis J k M) (x : ⨂[k] (_ : Fin p), M),
      (∀ e : Equiv.Perm (Fin p),
        PiTensorProduct.reindex k (fun _ : Fin p ↦ M) e x = x) →
      projectionForBasis k p B x = projection k p M x) ∧
    (∀ (h : M →ₗ[k] N) (x : ⨂[k] (_ : Fin p), M),
      (∀ e : Equiv.Perm (Fin p),
        PiTensorProduct.reindex k (fun _ : Fin p ↦ M) e x = x) →
      (∀ e : Equiv.Perm (Fin p),
        PiTensorProduct.reindex k (fun _ : Fin p ↦ N) e
          (PiTensorProduct.map (fun _ : Fin p ↦ h) x) =
            PiTensorProduct.map (fun _ : Fin p ↦ h) x) ∧
      projection k p N (PiTensorProduct.map (fun _ : Fin p ↦ h) x) =
        twistMap k p h (projection k p M x)) ∧
    (∀ (x : ⨂[k] (_ : Fin p), M) (y : ⨂[k] (_ : Fin p), N),
      (∀ e : Equiv.Perm (Fin p),
        PiTensorProduct.reindex k (fun _ : Fin p ↦ M) e x = x) →
      (∀ e : Equiv.Perm (Fin p),
        PiTensorProduct.reindex k (fun _ : Fin p ↦ N) e y = y) →
      (∀ e : Equiv.Perm (Fin p),
        PiTensorProduct.reindex k (fun _ : Fin p ↦ M ⊗[k] N) e
          (PiTensorProduct.map₂ (fun _ : Fin p ↦ TensorProduct.mk k M N) x y) =
            PiTensorProduct.map₂ (fun _ : Fin p ↦ TensorProduct.mk k M N) x y) ∧
      projection k p (M ⊗[k] N)
          (PiTensorProduct.map₂ (fun _ : Fin p ↦ TensorProduct.mk k M N) x y) =
        tensorComparison k p M N
          (projection k p M x ⊗ₜ[k] projection k p N y)) ∧
    (Functor.Monoidal.εIso (ModuleCat.extendScalars (frobenius k p))).inv
      (projection k p k (PiTensorProduct.tprod k (fun _ : Fin p ↦ (1 : k)))) = 1 := by
  sorry

end SymmetricInvariantFrobenius
