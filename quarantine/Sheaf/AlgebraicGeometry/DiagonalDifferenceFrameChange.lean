/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.DiagonalDifferenceFrameData
import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexExact
import Mathlib.LinearAlgebra.Matrix.Basis
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-! # Change of the ordered differential and normal frames

Source: current blueprint chart proof, Step 2; the change-of-frame calculation in
Step 8 of lem-pur-diagonal-difference-rees-frame.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Etale.FiniteSmoothPurity
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.DiagonalDifferenceReesFrame

private def differentialBasis {U V : Scheme.{u}} {d : ℕ} {h : U ⟶ V}
    [IsSeparated h] {x : ULift.{u} (Fin d) → Γ(U, ⊤)} (N : NormalFrame d h x) :
    Module.Basis (Fin d) Γ(U, ⊤) (h.relativeDifferentials.val.obj (op ⊤)) :=
  (Module.Basis.ofEquivFun
    ((appLinearEquivOfIso N.differentialFrame ⊤).symm.trans
      (freeSectionsEquivOpens ⊤ (ULift.{u} (Fin d))))).reindex Equiv.ulift

private theorem differentialBasis_value {U V : Scheme.{u}} {d : ℕ} {h : U ⟶ V}
    [IsSeparated h] {x : ULift.{u} (Fin d) → Γ(U, ⊤)} (N : NormalFrame d h x)
    (j : Fin d) :
    differentialBasis N j = h.relativeDifferentialsDerivation.d (X := op ⊤) (x (.up j)) := by
  classical
  let e := (appLinearEquivOfIso N.differentialFrame ⊤).symm.trans
    (freeSectionsEquivOpens ⊤ (ULift.{u} (Fin d)))
  have hv : differentialBasis N j = e.symm (Pi.single (ULift.up j) 1) := by
    exact (Module.Basis.reindex_apply (Module.Basis.ofEquivFun e) Equiv.ulift j).trans
      (congrFun (Module.Basis.coe_ofEquivFun e) (ULift.up j))
  rw [hv]
  change N.differentialFrame.hom.val.app (op ⊤)
    ((freeSectionsEquivOpens ⊤ (ULift.{u} (Fin d))).symm
      (Pi.single (ULift.up j) 1)) = _
  rw [show (freeSectionsEquivOpens ⊤ (ULift.{u} (Fin d))).symm
      (Pi.single (ULift.up j) 1) =
      (SheafOfModules.ιFree (R := U.ringCatSheaf) (ULift.up j)).val.app (op ⊤)
        (1 : Γ(U, ⊤)) by
    change (∑ i : ULift.{u} (Fin d),
      (SheafOfModules.ιFree (R := U.ringCatSheaf) i).val.app (op ⊤)
        ((Pi.single (ULift.up j) 1 : ULift.{u} (Fin d) → Γ(U, ⊤)) i)) = _
    simp only [Pi.single_apply]
    rw [Finset.sum_eq_single (ULift.up j)]
    · simp
    · intro i _ hi
      simp [hi]
    · simp]
  exact N.differentialFrame_value (.up j)

private theorem inverse_differential_eq {U V : Scheme.{u}} {d : ℕ} {h : U ⟶ V}
    [IsSeparated h] {x x' : ULift.{u} (Fin d) → Γ(U, ⊤)}
    (N : NormalFrame d h x) (N' : NormalFrame d h x') (a : Γ(U, ⊤)) :
    N.conormal.inv.val.app (op ⊤) (h.relativeDifferentialsDerivation.d (X := op ⊤) a) =
      N'.conormal.inv.val.app (op ⊤) (h.relativeDifferentialsDerivation.d (X := op ⊤) a) := by
  obtain ⟨b, hb, hn⟩ := N.sign a
  obtain ⟨b', hb', hn'⟩ := N'.sign a
  obtain ⟨e, he⟩ := (ConormalGradedAlgebra.presentation (pullback.diagonal h)).powerIdentification 1
  have hm : Mono (ConormalGradedAlgebra.powerInclusion (pullback.diagonal h) 1) := by
    rw [← he]
    infer_instance
  have hmval : Mono (ConormalGradedAlgebra.powerInclusion (pullback.diagonal h) 1).val :=
    (SheafOfModules.forget _).map_mono _
  have hbb : b = b' := PresheafOfModules.injective_of_mono
    (ConormalGradedAlgebra.powerInclusion (pullback.diagonal h) 1).val (op ⊤)
      (hb.trans hb'.symm)
  subst b'
  have hn₁ : N.conormal.hom.val.app (op ⊤)
      (ConormalGradedAlgebra.representative (pullback.diagonal h) 1 ⊤ b) =
        h.relativeDifferentialsDerivation.d (X := op ⊤) a := by simpa using hn
  have hn₂ : N'.conormal.hom.val.app (op ⊤)
      (ConormalGradedAlgebra.representative (pullback.diagonal h) 1 ⊤ b) =
        h.relativeDifferentialsDerivation.d (X := op ⊤) a := by simpa using hn'
  conv_lhs => rw [← hn₁]
  conv_rhs => rw [← hn₂]
  exact (congrArg (fun f ↦ f.val.app (op ⊤)
    (ConormalGradedAlgebra.representative (pullback.diagonal h) 1 ⊤ b))
      N.conormal.hom_inv_id).trans
        (congrArg (fun f ↦ f.val.app (op ⊤)
          (ConormalGradedAlgebra.representative (pullback.diagonal h) 1 ⊤ b))
            N'.conormal.hom_inv_id).symm

private theorem normal_coordinate_top {U V : Scheme.{u}} {d : ℕ} {h : U ⟶ V}
    [IsSeparated h] {x : ULift.{u} (Fin d) → Γ(U, ⊤)} (N : NormalFrame d h x)
    (j : Fin d) :
    N.normal.hom.appTop (AffineSpace.coord U (.up j)) =
      (coneAlgebraIso (pullback.diagonal h)).hom.right.hom.app (op ⊤)
        (((ConormalGradedAlgebra.presentation (pullback.diagonal h)).inclusion 1).val.app
          (op ⊤) (N.conormal.inv.val.app (op ⊤)
            (h.relativeDifferentialsDerivation.d (X := op ⊤) (x (.up j))))) := by
  have hn := N.normal_coordinate ⊤ (.up j)
  simpa [Scheme.Hom.appLE_top_top, N.differentialFrame_value] using hn

/-- Two ordered frames of relative differentials give inverse matrices, and their normal
coordinates transform by the same matrix. Source: the chart proof, Step 2 and its
change-of-frame computation (blueprint: lem-pur-diagonal-difference-frame-change).

Proof: take the matrices of the two bases of global differential sections. The
basis identities give inverse matrices. The positive difference normalization makes
the two inverse conormal comparisons agree on every da. Apply that comparison, the
degree-one inclusion and the relative-Spec counit to the basis expansion. The counit
is an algebra map over U, so its scalar action is pullback along the cone projection.
No rank or nonemptiness assumption is used. -/
theorem frame_change {U V : Scheme.{u}} {d : ℕ} {h : U ⟶ V} [IsSeparated h]
    {x x' : ULift.{u} (Fin d) → Γ(U, ⊤)}
    (N : NormalFrame d h x) (N' : NormalFrame d h x') :
    ∃ M H : Matrix (Fin d) (Fin d) Γ(U, ⊤),
      M * H = 1 ∧ H * M = 1 ∧
      (∀ j : Fin d, h.relativeDifferentialsDerivation.d (X := op ⊤) (x' (.up j)) =
        ∑ i : Fin d, M j i •
          h.relativeDifferentialsDerivation.d (X := op ⊤) (x (.up i))) ∧
      (∀ j : Fin d, N'.normal.hom.appTop (AffineSpace.coord U (.up j)) =
        ∑ i : Fin d,
          (PurityNormalBundle.projection (pullback.diagonal h)).appTop (M j i) *
            N.normal.hom.appTop (AffineSpace.coord U (.up i))) := by
  classical
  let b := differentialBasis N
  let b' := differentialBasis N'
  let M := (b.toMatrix b').transpose
  let H := (b'.toMatrix b).transpose
  have hM : M * H = 1 := by
    dsimp only [M, H]
    rw [← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]
  have hH : H * M = 1 := by
    dsimp only [M, H]
    rw [← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]
  have hd (j : Fin d) :
      h.relativeDifferentialsDerivation.d (X := op ⊤) (x' (.up j)) =
        ∑ i : Fin d, M j i •
          h.relativeDifferentialsDerivation.d (X := op ⊤) (x (.up i)) := by
    simpa only [M, Matrix.transpose_apply, b, b', differentialBasis_value] using
      (b.sum_toMatrix_smul_self b' j).symm
  refine ⟨M, H, hM, hH, hd, ?_⟩
  intro j
  rw [normal_coordinate_top, inverse_differential_eq N' N]
  simp_rw [normal_coordinate_top]
  rw [hd j, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.map_smul, _root_.map_smul]
  let A := (ConormalGradedAlgebra.presentation (pullback.diagonal h)).algebra
  let e := coneAlgebraIso (pullback.diagonal h)
  let z : A.right.obj.obj (op ⊤) :=
    ((ConormalGradedAlgebra.presentation (pullback.diagonal h)).inclusion 1).val.app
    (op ⊤) (N.conormal.inv.val.app (op ⊤)
      (h.relativeDifferentialsDerivation.d (X := op ⊤) (x (.up i))))
  change e.hom.right.hom.app (op ⊤) (A.hom.hom.app (op ⊤) (M j i) * z) = _
  rw [map_mul]
  congr 1
  exact congrArg (fun f ↦ f.hom.app (op ⊤) (M j i)) e.hom.w

end AlgebraicGeometry.DiagonalDifferenceReesFrame
