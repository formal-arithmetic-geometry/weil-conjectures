/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleMapFrameCoordinates

/-! # Comparing two vector-bundle frames after arbitrary base change

(blueprint: lem-pur-vector-integration-base-change-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

open Opposite VectorBundleZeroSection

attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom Matrix

private theorem freeMatrix_comp {W : Scheme.{u}} {I : Type u}
    [Fintype I] [DecidableEq I]
    (φ ψ : SheafOfModules.free (R := W.ringCatSheaf) I ⟶ SheafOfModules.free I) :
    Scheme.Modules.freeMatrix (φ ≫ ψ) =
      Scheme.Modules.freeMatrix ψ * Scheme.Modules.freeMatrix φ := by
  ext j i
  have h := congrFun (Scheme.Modules.freeSectionsEquiv_app ψ
    (Scheme.Modules.Hom.app (SheafOfModules.ιFree i ≫ φ) ⊤ (1 : Γ(W, ⊤)))) j
  change Scheme.Modules.Hom.app (Scheme.Modules.freeπ j) ⊤
    (Scheme.Modules.Hom.app ψ ⊤ (Scheme.Modules.Hom.app φ ⊤
      (Scheme.Modules.Hom.app (SheafOfModules.ιFree i) ⊤ (1 : Γ(W, ⊤))))) =
    ∑ x, Scheme.Modules.freeMatrix ψ j x * Scheme.Modules.freeMatrix φ x i at h
  exact h

private theorem freeMatrix_id {W : Scheme.{u}} {I : Type u} [DecidableEq I] :
    Scheme.Modules.freeMatrix (𝟙 (SheafOfModules.free (R := W.ringCatSheaf) I)) = 1 := by
  ext j i
  change Scheme.Modules.Hom.app (Scheme.Modules.freeπ j) ⊤
    (Scheme.Modules.Hom.app (SheafOfModules.ιFree i) ⊤ (1 : Γ(W, ⊤))) = _
  rw [Scheme.Modules.freeπ_app_ιFree_app]
  simp only [Matrix.one_apply, eq_comm]

private theorem tower_map_coordinate {W V : Scheme.{u}} (g : W ⟶ V) (r : ℕ)
    (j : Fin r) :
    (affineTraceMap g r).appTop (affineTraceCoordinate V r j) =
      affineTraceCoordinate W r j := by
  induction r with
  | zero => exact Fin.elim0 j
  | succ r ih =>
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simpa only [affineTraceCoordinate, Fin.lastCases_last, affineTraceMap] using!
        (AffineSpace.map_appTop_coord (affineTraceMap g r) PUnit.unit)
    · simp only [affineTraceCoordinate, Fin.lastCases_castSucc]
      change (affineTraceMap g (r + 1)).appTop
        ((AffineSpace PUnit.{u + 1} (affineTraceTower V r) ↘
          affineTraceTower V r).appTop (affineTraceCoordinate V r i)) = _
      erw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
      change ((AffineSpace.map PUnit.{u + 1} (affineTraceMap g r)) ≫
        AffineSpace PUnit.{u + 1} (affineTraceTower V r) ↘ affineTraceTower V r).appTop _ = _
      rw [AffineSpace.map_over, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ih]

/-- The two inverse frames over a common base differ by an invertible linear map.
This is an equality of scheme maps, with no coefficient ring, compact support,
Tate transport, projective-line datum, or counit.
Source: blueprint sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraph 2, base change and independence of the frame; the symmetric-algebra
construction and coordinate convention of def-asd-vector-bundle-zero-section.
(blueprint: lem-pur-vector-integration-base-change-coordinates).

Proof: pull the source frame along g and the target frame along a, using the free
module comparison for tensor pullback. The equality j f = g V.ι and a U.ι = j,
together with composition of module pullback, identify their modules over W.
Their composite is an automorphism of the rank-r free module. Its images of the
standard basis, and those of its inverse, give inverse matrices over Gamma(W,O_W).
This requires no affine hypothesis: maps out of the free sheaf are determined by
its standard global basis sections. In the convention e'_j = sum_i G_ij e_i,
the forward coordinate change is the transpose of G; take its inverse for the
inverse charts. Check the asserted equality on each degree-one generator of Sym(F).
The baseChange map takes generators to the module pullback unit, so both composites
have exactly the prescribed linear image. The symmetric-algebra universal property
and relative Spec identify the scheme maps. The coordinate-tower comparison converts
the polynomial substitution to affineTraceLinearMap. At rank zero the matrices
are empty and the equality is the equality of structural maps; for empty W the
same free-module and generator argument applies without a nonemptiness assumption.
-/
theorem vectorIntegration_baseChange_coordinates
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (r : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank r]
    (V : S.Opens) (eS : VectorBundleZeroSection.Trivialization S r F V)
    (U : T.Opens)
    (eT : VectorBundleZeroSection.Trivialization T r
      ((Scheme.Modules.tensorPullback f).obj F) U)
    (W : Scheme.{u}) (j : W ⟶ T) (a : W ⟶ U.toScheme) (g : W ⟶ V.toScheme)
    (ha : a ≫ U.ι = j) (hg : j ≫ f = g ≫ V.ι) :
    ∃ H : Matrix.GeneralLinearGroup (Fin r) Γ(W, ⊤),
      (affineTraceMap a r ≫ vectorIntegrationChart T r
        ((Scheme.Modules.tensorPullback f).obj F) U eT) ≫
          VectorTraceGeometry.baseChange f r F =
        affineTraceLinearMap W r H ≫
          (affineTraceMap g r ≫ vectorIntegrationChart S r F V eS) := by
  classical
  let G := (Scheme.Modules.tensorPullback f).obj F
  let m : (Scheme.Modules.pullback f).obj F ≅ G :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjointUniq
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))).app F
  have h : (a ≫ U.ι) ≫ f = g ≫ V.ι := by rw [ha, hg]
  let φ : SheafOfModules.free (R := W.ringCatSheaf) (ULift.{u} (Fin r)) ≅
      SheafOfModules.free (R := W.ringCatSheaf) (ULift.{u} (Fin r)) :=
    (pulledFrame S r F V eS g).symm ≪≫
      (Scheme.Modules.pullbackCongr h.symm).app F ≪≫
      (Scheme.Modules.pullbackComp (a ≫ U.ι) f).symm.app F ≪≫
      (Scheme.Modules.pullback (a ≫ U.ι)).mapIso m ≪≫
      pulledFrame T r G U eT a
  let C : Matrix (Fin r) (Fin r) Γ(W, ⊤) :=
    fun i j ↦ Scheme.Modules.freeMatrix φ.hom (ULift.up i) (ULift.up j)
  let D : Matrix (Fin r) (Fin r) Γ(W, ⊤) :=
    fun i j ↦ Scheme.Modules.freeMatrix φ.inv (ULift.up i) (ULift.up j)
  have hCD : C * D = 1 := by
    have he := freeMatrix_comp φ.inv φ.hom
    rw [φ.inv_hom_id, freeMatrix_id] at he
    ext i j
    have he' := congrArg (fun z ↦ z (ULift.up i) (ULift.up j)) he
    simp only [Matrix.mul_apply] at he'
    change (∑ z : Fin r, C i z * D z j) = _
    rw [← Equiv.sum_comp (Equiv.ulift : ULift.{u} (Fin r) ≃ Fin r)
      (fun z ↦ C i z * D z j)]
    simpa [C, D, Matrix.one_apply] using he'.symm
  have hDC : D * C = 1 := by
    have he := freeMatrix_comp φ.hom φ.inv
    rw [φ.hom_inv_id, freeMatrix_id] at he
    ext i j
    have he' := congrArg (fun z ↦ z (ULift.up i) (ULift.up j)) he
    simp only [Matrix.mul_apply] at he'
    change (∑ z : Fin r, D i z * C z j) = _
    rw [← Equiv.sum_comp (Equiv.ulift : ULift.{u} (Fin r) ≃ Fin r)
      (fun z ↦ D i z * C z j)]
    simpa [C, D, Matrix.one_apply] using he'.symm
  let H : Matrix.GeneralLinearGroup (Fin r) Γ(W, ⊤) :=
    { val := C.transpose
      inv := D.transpose
      val_inv := by rw [← Matrix.transpose_mul, hDC, Matrix.transpose_one]
      inv_val := by rw [← Matrix.transpose_mul, hCD, Matrix.transpose_one] }
  refine ⟨H, ?_⟩
  let ℓ := (affineTraceMap a r ≫ vectorIntegrationChart T r G U eT) ≫
    VectorTraceGeometry.baseChange f r F
  have hm : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ m.hom =
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app F :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ F
  have hv : VectorTraceGeometry.MapSpec f r r F G
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ m.hom)
      (VectorTraceGeometry.baseChange f r F) := by
    rw [hm]
    exact VectorTraceGeometry.map_spec f r r F G _
  have hℓ : ℓ ≫ π S r F = (affineTraceProjection W r ≫ g) ≫ V.ι := by
    simp only [ℓ, Category.assoc]
    rw [hv.comm, reassoc_of% (vectorIntegrationChart_isPullback T r G U eT).w,
      reassoc_of% (affineTraceMap_isPullback a r).w]
    simpa only [Category.assoc] using congrArg (fun z ↦ affineTraceProjection W r ≫ z) h
  let sq := (isPullback_morphismRestrict (π S r F) V).flip
  let k := sq.lift ℓ (affineTraceProjection W r ≫ g) hℓ
  have hk : k ≫ ((π S r F) ⁻¹ᵁ V).ι = ℓ := sq.lift_fst _ _ _
  have hkp : k ≫ ((π S r F) ∣_ V) = affineTraceProjection W r ≫ g :=
    sq.lift_snd _ _ _
  have ht : IsIso (trivializationMap S r F V eS) :=
    (trivializationMap_spec S r F V eS).1
  have he : k ≫ trivializationMap S r F V eS =
      affineTraceLinearMap W r H ≫ affineTraceMap g r ≫
        (affineTraceAffineSpaceIso V.toScheme r).hom := by
    apply AffineSpace.hom_ext
    · simp only [Category.assoc, (trivializationMap_spec S r F V eS).2.1,
        affineTraceAffineSpaceIso, asIso_hom, affineTraceToAffineSpace,
        AffineSpace.homOfVector_over]
      rw [hkp, (affineTraceMap_isPullback g r).w, ← Category.assoc,
        affineTraceLinearMap_over]
    · rintro ⟨j⟩
      have hc := map_frame_coordinates f r r F G m.hom
        (VectorTraceGeometry.baseChange f r F) hv V eS U eT W a g h k hk j
      rw [hc]
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        affineTraceAffineSpaceIso, asIso_hom, affineTraceToAffineSpace,
        AffineSpace.homOfVector_appTop_coord, tower_map_coordinate,
        affineTraceLinearMap_coordinate]
      rfl
  change ℓ = _
  rw [← hk]
  unfold vectorIntegrationChart
  simp only [← Category.assoc]
  apply congrArg (fun z ↦ z ≫ ((π S r F) ⁻¹ᵁ V).ι)
  apply (cancel_mono (trivializationMap S r F V eS)).mp
  simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using he

end AlgebraicGeometry.Etale
