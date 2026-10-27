/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.FieldTheory.FieldTower
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import WeilConjectures.FieldTheory.NormalExtensionFixedFieldPurelyInseparable
import WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions

/-!
# Finite normal envelopes of semilinear finite field actions

Source: Stacks Project, Fields, Tags 09I3, 09DT, 0EXM, 0BME (2), and 030M (2),
and the compatible-pair construction in the DAG proof
(blueprint: lem-sfb-finite-semilinear-field-envelope).

## Main definitions and statements

* `FiniteSemilinearFieldEnvelope` packages precisely the tower, compatible-pair group,
  projection, evaluation action, kernel identification, and fixed-field assertions.
* `exists_finiteSemilinearFieldEnvelope` asserts existence, including the separable upgrade.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

/-- Witnesses for the finite normal envelope of a possibly nonfaithful finite field action.
Source: Stacks Project, Fields, Tags 09I3, 09DT, 0EXM, 0BME (2), and 030M (2), together
with the explicit compatible-pair construction in the DAG proof.
(blueprint: lem-sfb-finite-semilinear-field-envelope)

The subgroup membership, projection, action, and kernel-equivalence equations specify the
canonical constructions, rather than an arbitrary extension group or action. The conditional
fields say that these same witnesses have the stronger properties when `L/K` is separable.
-/
structure FiniteSemilinearFieldEnvelope
    (K : Type u) (L : Type v) (H : Type w)
    [Field K] [Field L] [Algebra K L] [Group H] (A : H →* (K ≃+* K)) where
  /-- The fixed subfield `F = K^H`. -/
  base : Subfield K
  /-- This is exactly the fixed subfield, even when the action is not faithful. -/
  mem_base : ∀ x : K, x ∈ base ↔ ∀ h : H, A h x = x
  /-- The ambient extension field. -/
  carrier : Type (max u v)
  /-- Field operations on the ambient extension. -/
  [field : Field carrier]
  /-- The inclusion of the prescribed finite extension. -/
  [overL : Algebra L carrier]
  /-- The inclusion of `K` in the ambient extension. -/
  [overK : Algebra K carrier]
  /-- The inclusions agree on `K`. -/
  [towerK : IsScalarTower K L carrier]
  /-- The inclusion of the fixed base in the ambient extension. -/
  [overBase : Algebra base carrier]
  /-- The inclusions agree on the fixed base. -/
  [towerBase : IsScalarTower base K carrier]
  /-- The ambient field is finite over the fixed base. -/
  finiteBase : FiniteDimensional base carrier
  /-- The ambient field is normal over the fixed base. -/
  normalBase : Normal base carrier
  /-- The group `J`, with the inherited componentwise multiplication. -/
  pairs : Subgroup (H × (carrier ≃ₐ[base] carrier))
  /-- `J` consists exactly of compatible pairs. -/
  mem_pairs : ∀ p : H × (carrier ≃ₐ[base] carrier),
    p ∈ pairs ↔ ∀ k : K, p.2 (algebraMap K carrier k) = algebraMap K carrier (A p.1 k)
  /-- The projection to the original group, retaining its kernel of action. -/
  rho : pairs →* H
  /-- The projection is the first coordinate. -/
  rho_apply : ∀ j : pairs, rho j = j.val.1
  /-- There are finitely many compatible pairs. -/
  finitePairs : Finite pairs
  /-- Every original group element has a compatible lift. -/
  surjective_rho : Function.Surjective rho
  /-- The field action of the compatible-pair group. -/
  action : MulSemiringAction pairs carrier
  /-- The action is evaluation of the second coordinate. -/
  action_apply : ∀ (j : pairs) (m : carrier),
    @SMul.smul pairs carrier action.toSMul j m = j.val.2 m
  /-- On `K` the action agrees with the prescribed action. -/
  action_on_base : ∀ (j : pairs) (k : K),
    @SMul.smul pairs carrier action.toSMul j (algebraMap K carrier k) =
      algebraMap K carrier (A (rho j) k)
  /-- The canonical identification `Aut_K(M) ≃ ker(rho)`. -/
  kernelEquiv : (carrier ≃ₐ[K] carrier) ≃* rho.ker
  /-- The identification sends `sigma` to `(1, sigma)`. -/
  kernelEquiv_apply : ∀ sigma : carrier ≃ₐ[K] carrier,
    ((kernelEquiv sigma).val.val.1, (kernelEquiv sigma).val.val.2.toRingEquiv) =
      (1, sigma.toRingEquiv)
  /-- This identification respects the actions on the ambient field. -/
  kernelEquiv_action : ∀ (sigma : carrier ≃ₐ[K] carrier) (m : carrier),
    @SMul.smul pairs carrier action.toSMul (kernelEquiv sigma).val m = sigma m
  /-- The fixed field `M^N`, already containing `K`. -/
  fixed : IntermediateField K carrier
  /-- Membership in this field is precisely invariance under `N = ker(rho)`. -/
  mem_fixed : ∀ m : carrier,
    m ∈ fixed ↔ ∀ n : rho.ker,
      @SMul.smul pairs carrier action.toSMul n.val m = m
  /-- The fixed field is finite over `K`. -/
  finiteFixed : FiniteDimensional K fixed
  /-- The fixed field is purely inseparable over `K`. -/
  purelyInseparableFixed : IsPurelyInseparable K fixed
  /-- The original field is finite over its fixed base. -/
  finiteK : FiniteDimensional base K
  /-- The original field is Galois over its fixed base. -/
  galoisK : IsGalois base K
  /-- The ambient field is finite over `K`. -/
  finiteOverK : FiniteDimensional K carrier
  /-- The ambient field is normal over `K`. -/
  normalOverK : Normal K carrier
  /-- In the separable case the same ambient field is Galois over `F`. -/
  galoisBase_of_separable : Algebra.IsSeparable K L → IsGalois base carrier
  /-- In the separable case the same ambient field is Galois over `K`. -/
  galoisOverK_of_separable : Algebra.IsSeparable K L → IsGalois K carrier
  /-- In the separable case `M^N` is the image of `K`. -/
  fixed_eq_bot_of_separable : Algebra.IsSeparable K L → fixed = ⊥

/-- A finite extension admits a finite normal envelope retaining an arbitrary finite group
of semilinear automorphisms of its base field, including a nonfaithful group action.
Source: Stacks Project, Fields, Tags 09I3, 09DT, 0EXM, 0BME (2), and 030M (2).
(blueprint: lem-sfb-finite-semilinear-field-envelope)

Proof:
1. Replace the action by its image to apply `lem-wf-finite-field-action-fixed-degree`.
   The fixed field is unchanged, so `K/F` is finite Galois, and each `A h` fixes `F`.
2. Products of finite spanning sets show that `L/F` is finite. Apply
   `lem-weil-pbc-finite-extension-in-finite-normal-extension` to obtain `M/F` finite normal
   containing `L`, with the induced scalar tower.
3. Take exactly the subgroup of pairs `(h, sigma)` satisfying the displayed compatibility.
   Compatibility is stable under products and inverses. Project to the first coordinate
   and act on `M` by evaluation of the second coordinate; restriction to `K` is `A`.
4. `lem-weil-pbc-finite-extension-finitely-many-embeddings` makes `Aut_F(M)` finite, so
   the product with `H` and its subgroup `J` are finite.
5. `lem-weil-pbc-normal-subextension-automorphism-extends` lifts each `A h` to `M`;
   hence the projection onto `H` is surjective. No homomorphic choice of lifts is needed.
6. Its kernel consists exactly of `(1, sigma)` with `sigma` fixing `K`. The indicated
   maps between this kernel and `Aut_K(M)` are inverse homomorphisms and evaluate equally
   on `M`, so their fixed fields coincide.
7. `lem-weil-pbc-normal-extension-normal-over-intermediate` gives normality over `K`.
   A finite `F`-spanning set also spans over `K`. Apply
   `lem-weil-pbc-normal-extension-fixed-field-purely-inseparable` to identify `M^N/K`
   as purely inseparable; it is finite as a subspace of the finite-dimensional `M/K`.
8. If `L/K` is separable, `lem-zl-separable-permanence` makes `L/F` separable. Apply
   `lem-weil-pbc-finite-galois-receiving-separable-extensions` to the singleton family
   to choose `M/F` finite Galois, and perform the same compatible-pair construction.
9. `lem-sfb-separable-algebraic-intermediate-base` makes `M/K` separable, hence finite
   Galois. By `lem-weil-pbc-finite-galois-fixed-field`, its automorphisms fix exactly `K`.
   The kernel identification then gives `M^N = K` for these same witnesses.
-/
theorem exists_finiteSemilinearFieldEnvelope
    (K : Type u) (L : Type v) (H : Type w)
    [Field K] [Field L] [Algebra K L] [Group H]
    [FiniteDimensional K L] [Finite H] (A : H →* (K ≃+* K)) :
    Nonempty (FiniteSemilinearFieldEnvelope K L H A) := by
  sorry
