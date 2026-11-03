/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativePositiveWeilTensorPower
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeMiddleTensorEigenvalue
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Field.ULift

/-! # Tensor powers of eigenvalues on native middle-image stalks

Source: latest blueprint, sec-purity-real-sheaves/sk-p-real-semi/sk-p-real-semi.proof.md,
last paragraph, through the nonzero invariant tensor eigenvector.
(blueprint: lem-wf-native-middle-tensor-power-eigenvalue).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures.NativeL2
open NativeCondensedModule
open scoped TensorProduct

private theorem tensor_eigenvalue_of_intertwining
    {K V W Z : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup Z] [Module K Z]
    (f : V →ₗ[K] V) (g : W →ₗ[K] W) (h : Z →ₗ[K] Z)
    (t : V ⊗[K] W →ₗ[K] Z) (ht : Function.Injective t)
    (hcompat : ∀ v, h (t v) = t (TensorProduct.map f g v))
    (α β : K) (hα : Module.End.HasEigenvalue f α)
    (hβ : Module.End.HasEigenvalue g β) : Module.End.HasEigenvalue h (α * β) := by
  obtain ⟨v, hv, hv0⟩ := hα.exists_hasEigenvector
  obtain ⟨w, hw, hw0⟩ := hβ.exists_hasEigenvector
  have hnonzero : t (v ⊗ₜ w) ≠ 0 := by
    intro hz
    have hzero : v ⊗ₜ[K] w = 0 := ht (hz.trans (map_zero t).symm)
    obtain ⟨f', hf⟩ := Module.Projective.exists_dual_eq_one K hv0
    obtain ⟨g', hg⟩ := Module.Projective.exists_dual_eq_one K hw0
    have he := congrArg (TensorProduct.lid K K ∘ TensorProduct.map f' g') hzero
    simp [hf, hg] at he
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := t (v ⊗ₜ w))
  apply Module.End.hasEigenvector_iff.mpr
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hnonzero⟩
  rw [hcompat, TensorProduct.map_tmul,
    Module.End.mem_eigenspace_iff.mp hv, Module.End.mem_eigenspace_iff.mp hw,
    TensorProduct.smul_tmul_smul, map_smul]

private theorem middleWeilImage_tensor_hasEigenvalue
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {U₀ X₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [SmoothOfRelativeDimension 1 X₀.hom] [GeometricallyConnected X₀.hom]
    (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left] [IsDominant j₀.left]
    (M : WeilModule D l U₀)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (N : WeilModule D l U₀)
    (hN : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) N.carrier)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (α : ULift.{u + 1} (PadicAlgCl l))
    (hα : Module.End.HasEigenvalue
      (closedOperator D l X₀ (middleWeilImage D l j₀ M) x i hi).hom α)
    (β : ULift.{u + 1} (PadicAlgCl l))
    (hβ : Module.End.HasEigenvalue
      (closedOperator D l X₀ (middleWeilImage D l j₀ N) x i hi).hom β) :
    Module.End.HasEigenvalue
      (closedOperator D l X₀ (middleWeilImage D l j₀
        (CondensedFibreLinearCurrent.tensorWeil l (D.geometricFrobenius U₀) M N))
        x i hi).hom (α * β) := by
  obtain ⟨t, ht, hcompat⟩ :=
    middleWeilImage_tensor_injection D l hl j₀ M hM N hN x i hi
  exact tensor_eigenvalue_of_intertwining _ _ _ t ht hcompat α β hα hβ

set_option maxHeartbeats 400000 in
-- Allow kernel checking of the native stalk types in the recursive tensor induction.
/-- An eigenvalue on an ordinary middle-image stalk remains an eigenvalue after taking
its positive tensor power and then the ordinary middle image.
Source: latest blueprint, sk-p-real-semi.proof.md, last paragraph
(blueprint: lem-wf-native-middle-tensor-power-eigenvalue).

Proof: induct on n. The initial positive power is the original module. For the
successor, use the injective Frobenius-compatible map from the tensor product of
the two middle-image fibres to the middle image of their tensor product. Choose
nonzero eigenvectors for alpha and alpha^(n+1). Their pure tensor is nonzero:
linear functionals taking the two vectors to one send the tensor to one. Its
image under the injective map is therefore nonzero. Frobenius compatibility
makes it an eigenvector for alpha * alpha^(n+1) = alpha^(n+2). -/
theorem middleWeilImage_tensorPower_hasEigenvalue
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {U₀ X₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [SmoothOfRelativeDimension 1 X₀.hom] [GeometricallyConnected X₀.hom]
    (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left] [IsDominant j₀.left]
    (M : WeilModule D l U₀)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (α : ULift.{u + 1} (PadicAlgCl l))
    (hα : Module.End.HasEigenvalue
      (closedOperator D l X₀ (middleWeilImage D l j₀ M) x i hi).hom α) (n : ℕ) :
    Module.End.HasEigenvalue
      (closedOperator D l X₀
        (middleWeilImage D l j₀ (positiveWeilTensorPower D l U₀ M n)) x i hi).hom
      (α ^ (n + 1)) := by
  induction n with
  | zero =>
    simpa only [positiveWeilTensorPower, Nat.zero_add, pow_one] using hα
  | succ n hn =>
    change Module.End.HasEigenvalue
      (closedOperator D l X₀ (middleWeilImage D l j₀
        (CondensedFibreLinearCurrent.tensorWeil l (D.geometricFrobenius U₀)
          M (positiveWeilTensorPower D l U₀ M n))) x i hi).hom (α ^ (n + 1 + 1))
    rw [pow_succ']
    exact middleWeilImage_tensor_hasEigenvalue D l hl j₀ M hM
      (positiveWeilTensorPower D l U₀ M n)
      (positiveWeilTensorPower_properties D l U₀ M hM n).1 x i hi α hα _ hn

end WeilConjectures.NativeL2
