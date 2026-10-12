/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.RingTheory.TensorProduct.Maps
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule

/-!
# Tensor products and internal homs of Frobenius modules

The tensor product `M ⊗ N` of two Frobenius modules carries the Frobenius `F_M ⊗ F_N`, and the
space of linear maps `Hom(M, N)` the Frobenius `X ↦ F_N ∘ X ∘ F_M⁻¹`. The two are related by the
Frobenius-equivariant isomorphism `Hom(M^∨, N) ≅ M ⊗ N`.

Over an algebraically closed field, the eigenvalues of `F_M ⊗ F_N` are exactly the products
`a b` of an eigenvalue `a` of `F_M` and an eigenvalue `b` of `F_N`. Consequently weights add
under tensor products.

## Main declarations

- `Module.End.hasEigenvalue_map_mul`: `a b` is an eigenvalue of `f ⊗ g`.
- `Module.End.exists_hasEigenvalue_mul_of_hasEigenvalue_map`: every eigenvalue of `f ⊗ g`, `f`
  invertible, is such a product.
- `FrobeniusModule.tensor`, `FrobeniusModule.hom`: the tensor product and the internal hom.
- `FrobeniusModule.homDualEquiv`: `Hom(M^∨, N) ≅ M ⊗ N`.
- `FrobeniusModule.HasWeightsAtMost.tensor`, `FrobeniusModule.IsPureOfWeight.tensor`: weights
  of tensor products.
-/

@[expose] public section

universe u v t

open TensorProduct

namespace Module.End

variable {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W]

/-- If `a` is an eigenvalue of `f` and `b` one of `g`, then `a b` is an eigenvalue of `f ⊗ g`:
the tensor product of eigenvectors is an eigenvector. -/
theorem hasEigenvalue_map_mul {f : End K V} {g : End K W} {a b : K} (ha : f.HasEigenvalue a)
    (hb : g.HasEigenvalue b) : HasEigenvalue (TensorProduct.map f g) (a * b) :=
  sorry

/-- Over an algebraically closed field, every eigenvalue `μ` of `f ⊗ g` on `V ⊗ W`, for `f`
invertible and `V`, `W` finite-dimensional, is a product `a b` of an eigenvalue `a` of `f` and an
eigenvalue `b` of `g`. -/
theorem exists_hasEigenvalue_mul_of_hasEigenvalue_map [IsAlgClosed K] [FiniteDimensional K V]
    [FiniteDimensional K W] (f : V ≃ₗ[K] V) (g : End K W) {μ : K}
    (h : HasEigenvalue (TensorProduct.map f.toLinearMap g) μ) :
    ∃ a b, HasEigenvalue (f : End K V) a ∧ g.HasEigenvalue b ∧ μ = a * b :=
  sorry

end Module.End

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- The tensor product `M ⊗ N` of two Frobenius modules, with the Frobenius `F_M ⊗ F_N`. -/
noncomputable def tensor (M : FrobeniusModule.{u, v} K) (N : FrobeniusModule.{t, v} K) :
    FrobeniusModule.{max u t, v} K where
  carrier := M.carrier ⊗[K] N.carrier
  frobenius := TensorProduct.congr M.frobenius N.frobenius

lemma tensor_frobenius_tmul (M : FrobeniusModule.{u, v} K) (N : FrobeniusModule.{t, v} K)
    (x : M.carrier) (y : N.carrier) :
    (M.tensor N).frobenius (x ⊗ₜ y) = M.frobenius x ⊗ₜ N.frobenius y :=
  rfl

lemma frobeniusEnd_tensor (M : FrobeniusModule.{u, v} K) (N : FrobeniusModule.{t, v} K) :
    (M.tensor N).frobeniusEnd = TensorProduct.map M.frobeniusEnd N.frobeniusEnd :=
  sorry

/-- The internal hom `Hom(M, N)` of two Frobenius modules, with the Frobenius
`X ↦ F_N ∘ X ∘ F_M⁻¹`. -/
noncomputable def hom (M : FrobeniusModule.{u, v} K) (N : FrobeniusModule.{t, v} K) :
    FrobeniusModule.{max u t, v} K where
  carrier := M.carrier →ₗ[K] N.carrier
  frobenius := M.frobenius.arrowCongr N.frobenius

lemma hom_frobenius_apply (M : FrobeniusModule.{u, v} K) (N : FrobeniusModule.{t, v} K)
    (X : M.carrier →ₗ[K] N.carrier) :
    ((M.hom N).frobenius X : M.carrier →ₗ[K] N.carrier) =
      N.frobenius.toLinearMap ∘ₗ X ∘ₗ M.frobenius.symm.toLinearMap :=
  rfl

/-- Isomorphisms of Frobenius modules induce an isomorphism of internal homs. -/
def Equiv.homCongr {M M' : FrobeniusModule.{u, v} K} {N N' : FrobeniusModule.{t, v} K}
    (e₁ : M.Equiv M') (e₂ : N.Equiv N') : (M.hom N).Equiv (M'.hom N') :=
  sorry

/-- The Frobenius-equivariant isomorphism `Hom(M^∨, N) ≅ M ⊗ N`: `x ⊗ y` corresponds to the map
`φ ↦ φ(x) y`. -/
noncomputable def homDualEquiv (M N : FrobeniusModule.{max u v, v} K) :
    (M.dual.hom N).Equiv (M.tensor N) :=
  sorry

/-- `homDualEquiv` sends the map `φ ↦ φ(x) y` to `x ⊗ y`. -/
lemma homDualEquiv_symm_tmul (M N : FrobeniusModule.{max u v, v} K) (x : M.carrier)
    (y : N.carrier) (φ : Module.Dual K M.carrier) :
    (show M.dual.carrier →ₗ[K] N.carrier from
      (homDualEquiv M N).toLinearEquiv.symm (x ⊗ₜ y)) φ =
      φ x • y :=
  sorry

/-- `a b` is an eigenvalue of the Frobenius of `M ⊗ N` if `a` is one of `M` and `b` one of `N`.
-/
theorem hasEigenvalue_tensor_mul {M : FrobeniusModule.{u, v} K} {N : FrobeniusModule.{t, v} K}
    {a b : K} (ha : M.frobeniusEnd.HasEigenvalue a) (hb : N.frobeniusEnd.HasEigenvalue b) :
    (M.tensor N).frobeniusEnd.HasEigenvalue (a * b) :=
  sorry

/-- Over an algebraically closed field, the eigenvalues of the Frobenius of `M ⊗ N` are the
products of eigenvalues of `M` and of `N`. -/
theorem exists_of_hasEigenvalue_tensor [IsAlgClosed K] {M : FrobeniusModule.{u, v} K}
    {N : FrobeniusModule.{t, v} K} {μ : K} (h : (M.tensor N).frobeniusEnd.HasEigenvalue μ) :
    ∃ a b, M.frobeniusEnd.HasEigenvalue a ∧ N.frobeniusEnd.HasEigenvalue b ∧ μ = a * b :=
  sorry

/-- Weights at most `w` and `w'` give weights at most `w + w'` on the tensor product. -/
theorem HasWeightsAtMost.tensor [IsAlgClosed K] {ι : K →+* ℂ} {q : ℕ} (hq : 0 < q)
    {M : FrobeniusModule.{u, v} K} {N : FrobeniusModule.{t, v} K} {w w' : ℝ}
    (hM : M.HasWeightsAtMost ι q w) (hN : N.HasWeightsAtMost ι q w') :
    (M.tensor N).HasWeightsAtMost ι q (w + w') :=
  sorry

/-- The tensor product of modules pure of weights `w` and `w'` is pure of weight `w + w'`. -/
theorem IsPureOfWeight.tensor [IsAlgClosed K] {ι : K →+* ℂ} {q : ℕ} (hq : 0 < q)
    {M : FrobeniusModule.{u, v} K} {N : FrobeniusModule.{t, v} K} {w w' : ℝ}
    (hM : M.IsPureOfWeight ι q w) (hN : N.IsPureOfWeight ι q w') :
    (M.tensor N).IsPureOfWeight ι q (w + w') :=
  sorry

end FrobeniusModule
