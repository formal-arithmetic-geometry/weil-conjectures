/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedFibreLinearCurrent.CondensedFibreLinearOperationsStatement
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Dual.Defs
import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.RealPurityNativeFibreRank
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.RealPurityNativeLisseClosure

/-! # The inverse eigenvalue in the contragredient fibre

Source: sk-p-real-purity, dual paragraph
(blueprint: lem-rp-native-dual-eigenvalue).
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open Module

namespace WeilConjectures.NativeL2

/-- A finite-dimensional operator intertwined with the inverse transpose of an
isomorphism has the inverse of each original eigenvalue.
Source: sk-p-real-purity, dual paragraph, the eigenvalue alpha inverse
(blueprint: lem-rp-native-dual-eigenvalue).

Proof: an eigenvector for an invertible map has nonzero eigenvalue. Applying the
inverse map to its eigenvector equation gives the inverse eigenvalue. Transposition
preserves the characteristic polynomial, and an intertwining linear equivalence
identifies eigenvectors. -/
theorem inverse_eigenvalue_of_dual_comparison
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {W : Type w} [AddCommGroup W] [Module K W]
    (A : V ≃ₗ[K] V) (B : W →ₗ[K] W) (e : W ≃ₗ[K] Module.Dual K V)
    (hcomp : ∀ f v, e (B f) v = e f (A.symm v))
    {α : K} (hα : Module.End.HasEigenvalue A.toLinearMap α) :
    Module.End.HasEigenvalue B α⁻¹ := by
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  have hAv : A v = α • v := hv.apply_eq_smul
  have hne : α ≠ 0 := by
    intro hz
    apply hv.2
    apply A.injective
    simpa only [hz, zero_smul, map_zero] using hAv
  have hinv : Module.End.HasEigenvalue A.symm.toLinearMap α⁻¹ := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv.2⟩
    rw [Module.End.mem_eigenspace_iff]
    change A.symm v = α⁻¹ • v
    apply A.injective
    simp only [LinearEquiv.apply_symm_apply, map_smul, hAv, smul_smul,
      inv_mul_cancel₀ hne, one_smul]
  have hdual : Module.End.HasEigenvalue A.symm.toLinearMap.dualMap α⁻¹ := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, LinearMap.charpoly_dualMap]
    exact (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp hinv
  obtain ⟨f, hf⟩ := hdual.exists_hasEigenvector
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := e.symm f) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    apply e.injective
    ext x
    simpa only [hcomp, LinearEquiv.apply_symm_apply, map_smul,
      LinearMap.smul_apply, LinearMap.dualMap_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_toLinearMap] using
        congrArg (fun g : Module.Dual K V ↦ g x) hf.apply_eq_smul
  · intro hz
    apply hf.2
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using congrArg e hz

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open NativeCondensedModule
open scoped CategoryTheory.Obj

private theorem inverse_eigenvalue_of_module_iso
    {K : Type u} [Field K] {V W : ModuleCat.{v} K}
    [FiniteDimensional K V] (A : V ≅ V) (B : W ⟶ W)
    (e : W ≃ₗ[K] Module.Dual K V)
    (hcomp : ∀ f v, e (B f) v = e f (A.inv v))
    {α : K} (hα : Module.End.HasEigenvalue A.hom.hom α) :
    Module.End.HasEigenvalue B.hom α⁻¹ := by
  exact inverse_eigenvalue_of_dual_comparison A.toLinearEquiv B.hom e hcomp hα

private theorem dual_operator_hasEigenvalue_inv
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [IsAlgClosed D.k]
    {T : Scheme.{u}} (g : T ≅ T)
    (M : CategoryTheory.Endofunctor.IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom))
    (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower g.hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z)
    (c : CondensedFibreLinearCurrent.Comparisons l D g z)
    (hc : CondensedFibreLinearCurrent.WeilCompatibility l D g z n h c)
    (hcon : IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T M.carrier)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    [FiniteDimensional (ULift.{u + 1} (PadicAlgCl l)) (fibre l D M.carrier z)]
    (α : ULift.{u + 1} (PadicAlgCl l))
    (hα : Module.End.HasEigenvalue (operator l D g.hom M.carrier M.str z n h).hom α) :
    Module.End.HasEigenvalue
      (operator l D g.hom (CondensedFibreLinearCurrent.dualWeil l g M).carrier
        (CondensedFibreLinearCurrent.dualWeil l g M).str z n h).hom α⁻¹ := by
  exact inverse_eigenvalue_of_module_iso
    (transport l D g.hom M.carrier M.str z z n h) _
    (c.dual M hcon hM) (hc.dual_frobenius M hcon hM) hα

set_option maxHeartbeats 800000 in
-- The canonical transport comparison has dependent condensed coefficient types.
attribute [local irreducible] CondensedRing.upperStar in
/-- A local Frobenius eigenvalue on a lisse native Weil module becomes its inverse
on the actual internal dual, using the specified evaluation comparison.
Source: sk-p-real-purity, dual paragraph
(blueprint: lem-rp-native-dual-eigenvalue).

Proof: apply the existing tensor/dual fibre comparison at the closed point. Its
Frobenius compatibility identifies the dual operator with the inverse transpose of
the original transport isomorphism. The actual fibre is finite-dimensional, and the
linear-algebra inverse-eigenvalue lemma applies. No duality of derived complexes is used. -/
theorem closedOperator_dual_hasEigenvalue_inv
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [IsSeparated X₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (M : WeilModule D l X₀)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (α : ULift.{u + 1} (PadicAlgCl l))
    (hα : Module.End.HasEigenvalue (closedOperator D l X₀ M x i hi).hom α) :
    Module.End.HasEigenvalue (closedOperator D l X₀
      (CondensedFibreLinearCurrent.dualWeil l (D.geometricFrobenius X₀) M) x i hi).hom
      α⁻¹ := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : IsNoetherian (D.geometricFiber X₀).left := {
    toIsLocallyNoetherian := by
      change IsLocallyNoetherian (pullback X₀.hom _)
      infer_instance
    toCompactSpace := by
      change CompactSpace ↥(pullback X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) : Scheme.{u})
      infer_instance }
  have hcon := native_constructible_of_lisse l _ M.carrier hM
  obtain ⟨c, hc⟩ :=
    (CondensedFibreLinearCurrent.condensed_fibre_linear_operations D l hl X₀).2.2 x i hi
  have := native_fibre_finite_of_lisse D l M.carrier hM
    (localClosedPoint D X₀ x i hi)
  unfold closedOperator at hα ⊢
  exact dual_operator_hasEigenvalue_inv D l (D.geometricFrobenius X₀) M
    (localClosedPoint D X₀ x i hi) (localClosedPointDegree D X₀ x - 1)
    (localClosedPoint_return D X₀ x i hi) c hc hcon hM α hα

end WeilConjectures.NativeL2
