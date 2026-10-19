/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tame invariants and arbitrary base change

Source: Stacks Project, Tags 0H36 and 0BRH, with the Reynolds idempotent argument
for arbitrary scalar rings (blueprint: lem-per-tame-invariants-arbitrary-base-change).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w uB uB' uC wN

open TensorProduct
open Representation

namespace AlgebraicGeometry

/-- The map induced on invariant submodules by an equivariant linear map.

Source: Stacks Project, Tag 0H36, the functoriality clause of the averaging argument.
(blueprint: lem-per-tame-invariants-arbitrary-base-change) -/
noncomputable def invariantLinearMap
    {A : Type u} [CommRing A] {G : Type v} [Group G]
    {M : Type w} {N : Type wN} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (ρ : Representation A G M) (σ : Representation A G N)
    (f : M →ₗ[A] N)
    (hcomm : ∀ g : G, f.comp (ρ g) = (σ g).comp f) :
    ρ.invariants →ₗ[A] σ.invariants :=
  (f.comp ρ.invariants.subtype).codRestrict σ.invariants (fun x => by
    rw [Representation.mem_invariants]
    intro g
    have hfg : f (ρ g x) = σ g (f x) := LinearMap.congr_fun (hcomm g) x
    exact hfg.symm.trans (congrArg f (x.property g)))

/-- The fixed submodule of scalar extension, with the action trivial on `B`.

Source: Stacks Project, Tag 0H36, Reynolds base-change argument.
(blueprint: lem-per-tame-invariants-arbitrary-base-change) -/
def tameBaseChangeFixedSubmodule
    {A : Type u} [CommRing A] {G : Type v} [Group G]
    {M : Type w} [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (B : Type uB) [CommRing B] [Algebra A B] :
    Submodule B (B ⊗[A] M) :=
  ⨅ g : G, LinearMap.eqLocus (LinearMap.baseChange B (ρ g)) LinearMap.id

/-- The canonical tensor of the invariant inclusion, corestricted to fixed elements.

Source: Stacks Project, Tag 0H36, Reynolds base-change argument: on pure tensors
this sends `b ⊗ x` to `b ⊗ x`, whose second factor is fixed.
(blueprint: lem-per-tame-invariants-arbitrary-base-change) -/
noncomputable def tameInvariantsBaseChangeMap
    {A : Type u} [CommRing A] {G : Type v} [Group G]
    {M : Type w} [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (B : Type uB) [CommRing B] [Algebra A B] :
    (B ⊗[A] ρ.invariants) →ₗ[B] tameBaseChangeFixedSubmodule ρ B :=
  (TensorProduct.AlgebraTensorModule.map LinearMap.id ρ.invariants.subtype).codRestrict
    (tameBaseChangeFixedSubmodule ρ B) (fun z ↦ by
      simp only [tameBaseChangeFixedSubmodule, Submodule.mem_iInf, LinearMap.mem_eqLocus]
      intro g
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul b x => simp [x.property g]
      | add x y hx hy => simp only [map_add, hx, hy])

/-- The fixed `B`-subalgebra of `B ⊗[A] C` for the action on the second factor.

Source: Stacks Project, Tags 0H36 and 00CV. The intersection of the equalizers
of `id ⊗ g` and the identity is the fixed subalgebra.
(blueprint: lem-per-tame-invariants-arbitrary-base-change) -/
def tameBaseChangeFixedSubalgebra
    {A : Type u} [CommRing A] {G : Type v} [Group G]
    (B : Type uB) [CommRing B] [Algebra A B]
    (C : Type uC) [CommRing C] [Algebra A C] [MulSemiringAction G C]
    [SMulCommClass G A C] : Subalgebra B (B ⊗[A] C) :=
  ⨅ g : G, AlgHom.equalizer
    (Algebra.TensorProduct.map (AlgHom.id B B) (MulSemiringAction.toAlgHom A C g))
    (AlgHom.id B (B ⊗[A] C))

/-- The canonical tensor of the fixed-subalgebra inclusion, corestricted to fixed elements.

Source: Stacks Project, Tags 0H36 and 00CV. On pure tensors this is `b ⊗ x ↦ b ⊗ x`;
the image is fixed since each second factor is fixed.
(blueprint: lem-per-tame-invariants-arbitrary-base-change) -/
noncomputable def tameInvariantsAlgebraBaseChangeMap
    {A : Type u} [CommRing A] {G : Type v} [Group G]
    (B : Type uB) [CommRing B] [Algebra A B]
    (C : Type uC) [CommRing C] [Algebra A C] [MulSemiringAction G C]
    [SMulCommClass G A C] :
    (B ⊗[A] FixedPoints.subalgebra A C G) →ₐ[B]
      tameBaseChangeFixedSubalgebra (A := A) (G := G) B C :=
  (Algebra.TensorProduct.map (AlgHom.id B B)
    (FixedPoints.subalgebra A C G).val).codRestrict
      (tameBaseChangeFixedSubalgebra (A := A) (G := G) B C) (fun z ↦ by
        simp only [tameBaseChangeFixedSubalgebra, Algebra.mem_iInf, AlgHom.mem_equalizer]
        intro g
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul b x =>
          change b ⊗ₜ[A] (g • (x : C)) = b ⊗ₜ[A] (x : C)
          rw [x.property g]
        | add x y hx hy => simp only [map_add, hx, hy])

/-- Tame invariants commute with arbitrary base change when the group order is invertible.

Source: Stacks Project, Tag 0H36 (remark-when-iso), compared with Tag 0BRH
(lemma-base-change-invariants); the algebra clause uses Tag 00CV.
(blueprint: lem-per-tame-invariants-arbitrary-base-change)

Proof: average the finite group action with the inverse of its cardinality. Reindexing
shows that this operator has image the invariant submodule and is the identity there.
Base change the inclusion and averaging retraction using the tensor-product universal
property. Their composites are the identity and the base-changed averaging projector,
so the canonical tensor map is an isomorphism without a flatness hypothesis. The same
pure-tensor formulas prove naturality in equivariant maps and in the scalar algebra.
For an algebra action, fixed elements form a subalgebra and the comparison preserves
multiplication, giving the asserted algebra isomorphism.
-/
theorem tame_invariants_arbitrary_base_change
    {A : Type u} [CommRing A]
    {G : Type v} [Group G] [Fintype G]
    {M : Type w} [AddCommGroup M] [Module A M]
    (ρ : Representation A G M)
    (d : ℕ) (hd : Fintype.card G = d) (hunit : IsUnit (d : A)) :
    (
      (((↑(hunit.unit⁻¹) : A) • (∑ g : G, ρ g)).comp
          ((↑(hunit.unit⁻¹) : A) • (∑ g : G, ρ g))) =
        ((↑(hunit.unit⁻¹) : A) • (∑ g : G, ρ g)) ∧
      Set.range ((↑(hunit.unit⁻¹) : A) • (∑ g : G, ρ g)) =
        (ρ.invariants : Set M) ∧
      (∀ x : ρ.invariants,
        ((↑(hunit.unit⁻¹) : A) • (∑ g : G, ρ g)) x = x)
    ) ∧
    (∀ (B : Type uB) [CommRing B] [Algebra A B],
      Function.Bijective (tameInvariantsBaseChangeMap ρ B)) ∧
    (∀ (B : Type uB) [CommRing B] [Algebra A B]
      (B' : Type uB') [CommRing B'] [Algebra A B']
      (vB : B →ₐ[A] B') (x : B ⊗[A] ρ.invariants),
      TensorProduct.map vB.toLinearMap (LinearMap.id (R := A) (M := M))
          (tameInvariantsBaseChangeMap ρ B x : B ⊗[A] M) =
        (tameInvariantsBaseChangeMap ρ B'
          (TensorProduct.map vB.toLinearMap
            (LinearMap.id (R := A) (M := ρ.invariants)) x) : B' ⊗[A] M)) ∧
    (∀ (N : Type wN) [AddCommGroup N] [Module A N]
      (σ : Representation A G N) (f : M →ₗ[A] N)
      (hcomm : ∀ g : G, f.comp (ρ g) = (σ g).comp f)
      (B : Type uB) [CommRing B] [Algebra A B] (x : B ⊗[A] ρ.invariants),
      (tameInvariantsBaseChangeMap σ B
          (TensorProduct.AlgebraTensorModule.map (LinearMap.id (R := B) (M := B))
            (invariantLinearMap ρ σ f hcomm) x) : B ⊗[A] N) =
        TensorProduct.AlgebraTensorModule.map (LinearMap.id (R := B) (M := B)) f
          (tameInvariantsBaseChangeMap ρ B x : B ⊗[A] M)) ∧
    (∀ (B : Type uB) [CommRing B] [Algebra A B]
      (C : Type uC) [CommRing C] [Algebra A C] [MulSemiringAction G C]
      [SMulCommClass G A C],
      Function.Bijective (tameInvariantsAlgebraBaseChangeMap (A := A) (G := G) B C)) := by
  sorry

end AlgebraicGeometry
