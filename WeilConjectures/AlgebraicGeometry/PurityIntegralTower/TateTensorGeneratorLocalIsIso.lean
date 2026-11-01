/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.CondensedTateIntegralTowerData
import all WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateLocalRootTensorsExt
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootLocalModels
import all WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientModelsOrdinaryExistence
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ProEtaleSheafificationTensorComparison
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import all WeilConjectures.AlgebraicGeometry.Comparison.ComparisonPureSections
import all WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
import all WeilConjectures.SmoothPurity.PurStrictScalar.ScalarReductionTowerBalancing

/-! Pointwise local invertibility of the normalized Tate tensor map.

Source: smooth-purity transport, normalized Tate tower, Step 2.
(blueprint: lem-pur-tate-tensor-generator-local-isiso)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

private theorem component_isIso
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {M N : SheafOfModules.{u + 1} R}
    (e : M ≅ N) (W : Cᵒᵖ) : IsIso (e.hom.val.app W) :=
  Functor.map_isIso (SheafOfModules.evaluation R W) e.hom

private theorem component_injective
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {M N : SheafOfModules.{u + 1} R}
    (e : M ≅ N) (W : Cᵒᵖ) : Function.Injective (e.hom.val.app W) := by
  have := component_isIso e W
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

private theorem component_inv_hom
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {M N : SheafOfModules.{u + 1} R}
    (e : M ≅ N) (W : Cᵒᵖ) (x : N.val.obj W) :
    e.hom.val.app W (e.inv.val.app W x) = x := by
  exact congrArg (fun f ↦ f.val.app W x) e.inv_hom_id

private theorem extension_pure
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M : pbcModules T R) (W : T.ProEtᵒᵖ)
    (s : S.obj.obj W) (x : M.val.obj W) :
    (eqToIso ((pbcExtensionExistence φ).choose_spec.choose M)).hom.val.app W
        (pbcTensorSection φ M W s x) =
      SheafOfModules.scalarExtensionConstraintTmul φ M W x s := by
  let h := (pbcExtensionExistence φ).choose_spec.choose M
  change (eqToHom h).val.app W ((eqToHom h.symm).val.app W _) = _
  have hi := congrArg (fun f ↦ f.val.app W
      (SheafOfModules.scalarExtensionConstraintTmul φ M W x s))
    (eqToIso h).inv_hom_id
  exact hi

set_option maxHeartbeats 2000000 in
-- Comparing the two transported coefficient actions requires substantial definitional reduction.
set_option maxHeartbeats 1000000 in
-- Tensor comparison crosses the fixed and variable coefficient module presentations.
private theorem quotient_tensor
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M N : pbcModules T R) :
    ∃ e : (pbcExtend φ).obj M ⊗ (pbcExtend φ).obj N ≅
        (pbcExtend φ).obj (M ⊗ N),
      ∀ (W : T.ProEtᵒᵖ) (s t : S.obj.obj W) (x : M.val.obj W) (y : N.val.obj W),
        e.hom.val.app W
          (SheafOfModules.scalarExtensionConstraintPureTensor S
            ((pbcExtend φ).obj M) ((pbcExtend φ).obj N) W
            (pbcTensorSection φ M W s x) (pbcTensorSection φ N W t y)) =
        pbcTensorSection φ (M ⊗ N) W (s * t)
          (SheafOfModules.scalarExtensionConstraintPureTensor R M N W x y) := by
  let c := (SheafOfModules.scalarExtension_constraint_coherence R S φ).some
  let a (H : pbcModules T R) : (pbcExtend φ).obj H ≅
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ H :=
    eqToIso ((pbcExtensionExistence φ).choose_spec.choose H)
  refine ⟨tensorIso (a M) (a N) ≪≫ (c.tensorIso M N).symm ≪≫ (a (M ⊗ N)).symm, ?_⟩
  intro W s t x y
  change (a (M ⊗ N)).inv.val.app W
    ((c.tensorIso M N).inv.val.app W
      (((a M).hom ⊗ₘ (a N).hom).val.app W _)) = _
  erw [SheafOfModules.pure_natural S (a M).hom (a N).hom W
    (pbcTensorSection φ M W s x) (pbcTensorSection φ N W t y)]
  erw [extension_pure T φ M W s x, extension_pure T φ N W t y,
    c.tensor_inv M N W x y s t]
  apply component_injective (a (M ⊗ N)) W
  change (a (M ⊗ N)).hom.val.app W ((a (M ⊗ N)).inv.val.app W _) = _
  rw [component_inv_hom]
  exact (extension_pure T φ (M ⊗ N) W (s * t) _).symm

private theorem quotient_unit
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) :
    ∃ e : SheafOfModules.unit ((adicLisseForget T).obj S) ≅
        (pbcExtend φ).obj (SheafOfModules.unit ((adicLisseForget T).obj R)),
      ∀ (W : T.ProEtᵒᵖ) (s : S.obj.obj W),
        e.hom.val.app W s = pbcTensorSection φ _ W s (1 : R.obj.obj W) := by
  let c := (SheafOfModules.scalarExtension_constraint_coherence R S φ).some
  let a : (pbcExtend φ).obj (SheafOfModules.unit ((adicLisseForget T).obj R)) ≅
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ
        (SheafOfModules.unit ((adicLisseForget T).obj R)) :=
    eqToIso ((pbcExtensionExistence φ).choose_spec.choose _)
  refine ⟨c.unitIso.symm ≪≫ a.symm, ?_⟩
  intro W s
  change a.inv.val.app W (c.unitIso.inv.val.app W s) = _
  rw [c.unit_inv]
  apply component_injective a W
  rw [component_inv_hom]
  exact (extension_pure T φ (SheafOfModules.unit ((adicLisseForget T).obj R))
    W s (1 : R.obj.obj W)).symm

set_option maxHeartbeats 2000000 in
-- Transporting the finite-root comparison through both realizations is definitionally expensive.
end AlgebraicGeometry.Scheme.PurityIntegralTower
