/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.RealWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativePositiveWeilTensorPower
import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights
import Mathlib.LinearAlgebra.TensorProduct.Basic
import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeConstructibleFibreFinite

/-! # Punctual bounds of native positive tensor powers

Source: latest blueprint, sec-purity-real-sheaves/sk-p-real-semi/sk-p-real-semi.proof.md,
last paragraph: F tensor k has punctual bound k*a.
(blueprint: lem-wf-native-tensor-punctual-weights).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures.NativeL2
open NativeCondensedModule

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom]

omit [IsSeparated U₀.hom] in
private theorem operator_bijective (M : WeilModule D l U₀)
    (x : {x : U₀.left // x ∈ closedPoints U₀.left})
    (i : U₀.left.residueField x.val →+* D.k)
    (hi : i.comp (U₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    Function.Bijective (closedOperator D l U₀ M x i hi).hom := by
  let F := closedOperator D l U₀ M x i hi
  have : IsIso F := by
    dsimp [F]
    unfold closedOperator operator
    infer_instance
  exact (asIso F).toLinearEquiv.bijective

include hl in
/-- Tensor products add punctual upper bounds on the actual native stalks. -/
private theorem tensorWeil_hasPunctualWeightsAtMost
    (M N : WeilModule D l U₀)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (hN : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) N.carrier)
    (ι : PadicAlgCl l →+* ℂ) (a b : ℝ)
    (ha : HasPunctualWeightsAtMost D l U₀ M ι a)
    (hb : HasPunctualWeightsAtMost D l U₀ N ι b) :
    HasPunctualWeightsAtMost D l U₀
      (CondensedFibreLinearCurrent.tensorWeil l (D.geometricFrobenius U₀) M N) ι
      (a + b) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let : IsAlgClosed (ULift.{u + 1} (PadicAlgCl l)) :=
    ⟨fun P ↦ Polynomial.Splits.of_splits_map ULift.ringEquiv.toRingHom
      (IsAlgClosed.splits _) (fun a _ ↦ ⟨ULift.up a, rfl⟩)⟩
  have : IsNoetherian (D.geometricFiber U₀).left :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
        (CategoryTheory.Limits.pullback.snd U₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
      toCompactSpace := by
        change CompactSpace (CategoryTheory.Limits.pullback U₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) : Scheme)
        infer_instance }
  have hMc := (positiveWeilTensorPower_properties D l U₀ M hM 0).2
  have hNc := (positiveWeilTensorPower_properties D l U₀ N hN 0).2
  intro x i hi γ hγ
  let := constructible_fibre_finiteDimensional D l M.carrier hMc
    (localClosedPoint D U₀ x i hi)
  let := constructible_fibre_finiteDimensional D l N.carrier hNc
    (localClosedPoint D U₀ x i hi)
  obtain ⟨c, hc⟩ := (CondensedFibreLinearCurrent.condensed_fibre_linear_operations
    D l hl U₀).2.2 x i hi
  let e := c.tensor M N hMc hNc hN
  have he (v) :
      e ((closedOperator D l U₀
        (CondensedFibreLinearCurrent.tensorWeil l (D.geometricFrobenius U₀) M N)
        x i hi).hom v) =
      TensorProduct.map (closedOperator D l U₀ M x i hi).hom
        (closedOperator D l U₀ N x i hi).hom (e v) := by
    simpa only [e, closedOperator, CondensedFibreLinearCurrent.tensorWeil,
      Endofunctor.IsoAlgebra.mk_carrier, Endofunctor.IsoAlgebra.mk_str] using
      hc.tensor_frobenius M N hMc hNc hN v
  have hγ' : Module.End.HasEigenvalue
      (TensorProduct.map (closedOperator D l U₀ M x i hi).hom
        (closedOperator D l U₀ N x i hi).hom) γ := by
    obtain ⟨v, hv, hv0⟩ := hγ.exists_hasEigenvector
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := e v)
    apply Module.End.hasEigenvector_iff.mpr
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · rw [← he, Module.End.mem_eigenspace_iff.mp hv, map_smul]
    · exact fun h ↦ hv0 (e.injective (h.trans (map_zero e).symm))
  exact LinearMap.tensor_frobeniusWeight_le (ι.comp ULift.ringEquiv.toRingHom)
    (Nat.card (U₀.left.residueField x.val)) _ _
    (operator_bijective D l U₀ M x i hi) (operator_bijective D l U₀ N x i hi)
    a b (fun α hα ↦ by simpa [WeilGroup.frobeniusWeight, ULift.ringEquiv] using ha x i hi α hα)
    (fun β hβ ↦ by simpa [WeilGroup.frobeniusWeight, ULift.ringEquiv] using hb x i hi β hβ) γ hγ'

include hl in
/-- The canonical monoidal fibre comparison intertwines local Frobenius operators.
The tensor spectrum is the multiset of products of the original spectra; logarithmic
weights add. Induction over the recursive tensor construction proves the claimed bound.
Source: latest blueprint, sk-p-real-semi.proof.md, final paragraph
(blueprint: lem-wf-native-tensor-punctual-weights). -/
theorem positiveWeilTensorPower_hasPunctualWeightsAtMost
    (M : WeilModule D l U₀)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (ι : PadicAlgCl l →+* ℂ) (a : ℝ)
    (ha : HasPunctualWeightsAtMost D l U₀ M ι a) (n : ℕ) :
    HasPunctualWeightsAtMost D l U₀ (positiveWeilTensorPower D l U₀ M n) ι
      ((n + 1 : ℕ) * a) := by
  induction n with
  | zero => simpa [positiveWeilTensorPower] using ha
  | succ n hn =>
    have h := tensorWeil_hasPunctualWeightsAtMost D l hl U₀ M _ hM
      (positiveWeilTensorPower_properties D l U₀ M hM n).1 ι a _ ha hn
    change HasPunctualWeightsAtMost D l U₀
      (CondensedFibreLinearCurrent.tensorWeil l (D.geometricFrobenius U₀) M
        (positiveWeilTensorPower D l U₀ M n)) ι _
    convert h using 1
    push_cast
    ring

end WeilConjectures.NativeL2
