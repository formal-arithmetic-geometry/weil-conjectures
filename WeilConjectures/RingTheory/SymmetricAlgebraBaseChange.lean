/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Localization.BaseChange

/-! # Symmetric algebras and base change

Source: Stacks Project, Algebra, Lemma 0C6F and the universal properties of symmetric
algebras and extension of scalars (blueprint: lem-weil-pbc-symmetric-algebra-base-change).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace SymmetricAlgebra

/-- The canonical base-change map for the symmetric algebra is an isomorphism.
Source: Stacks Project, Algebra, Lemma 0C6F, generalized by the universal properties
(blueprint: lem-weil-pbc-symmetric-algebra-base-change).

Proof: (1) The symmetric-algebra universal property
(lem-weil-pbc-symmetric-algebra-universal-property) constructs the unique `β` from the
linear map `m ↦ ι S (S ⊗[R] M) (1 ⊗ₜ m)`.
(2) The algebra base-change universal property
(lem-weil-pbc-algebra-tensor-base-change-universal-property) extends `β` to the displayed
`S`-algebra map, sending `s ⊗ₜ a` to `s • β a`.
(3) The module base-change universal property
(lem-weil-pbc-module-base-change-universal-property) extends `m ↦ 1 ⊗ₜ ι R M m` to
an `S`-linear map sending `s ⊗ₜ m` to `s ⊗ₜ ι R M m`. Extend this again by the
symmetric-algebra universal property to obtain the inverse algebra map.
(4) The forward map after the inverse is the identity on all degree-one generators;
symmetric-algebra uniqueness makes it the identity everywhere.
(5) For the other composite, algebra base-change uniqueness reduces to comparing maps
on `SymmetricAlgebra R M`; symmetric-algebra uniqueness reduces this to the generators,
where both maps send `ι R M m` to `1 ⊗ₜ ι R M m`. Thus both composites are identities. -/
theorem baseChange_bijective
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
    (β : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra S (S ⊗[R] M))
    (hβ : ∀ m : M, β (ι R M m) = ι S (S ⊗[R] M) (1 ⊗ₜ[R] m)) :
    Function.Bijective
      (AlgHom.liftEquiv R S (SymmetricAlgebra R M)
        (SymmetricAlgebra S (S ⊗[R] M)) β) := by
  let Φ := AlgHom.liftEquiv R S (SymmetricAlgebra R M)
    (SymmetricAlgebra S (S ⊗[R] M)) β
  let j : M →ₗ[R] S ⊗[R] SymmetricAlgebra R M :=
    Algebra.TensorProduct.includeRight.toLinearMap.comp (ι R M)
  let Ψ : SymmetricAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] SymmetricAlgebra R M :=
    lift (j.liftBaseChange S)
  have hΨ : ∀ s m, Ψ (ι S (S ⊗[R] M) (s ⊗ₜ[R] m)) =
      s ⊗ₜ[R] ι R M m := by
    intro s m
    simp [Ψ, j, TensorProduct.smul_tmul']
  have hright : Φ.comp Ψ = AlgHom.id S _ := by
    apply algHom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s m =>
      change Φ (Ψ (ι S (S ⊗[R] M) (s ⊗ₜ[R] m))) =
        ι S (S ⊗[R] M) (s ⊗ₜ[R] m)
      rw [hΨ, AlgHom.liftEquiv_tmul, hβ]
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  have hleft : Ψ.comp Φ = AlgHom.id S _ := by
    apply Algebra.TensorProduct.ext_ring
    apply algHom_ext
    apply LinearMap.ext
    intro m
    simp [Φ, hβ, hΨ]
  exact ⟨(show Function.LeftInverse Ψ Φ from fun x ↦ DFunLike.congr_fun hleft x).injective,
    (show Function.RightInverse Ψ Φ from fun x ↦ DFunLike.congr_fun hright x).surjective⟩


end SymmetricAlgebra
