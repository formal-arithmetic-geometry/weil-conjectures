/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Submission.WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualTowerCore
import Submission.WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement
import all Submission.WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualLocalIso
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Signed powers of lines: scalar, tensor and tower comparisons

Source: blueprint main-20261015, prop-weil-twist-preserves.proof.md, tensor-power/internal-Hom
and common-finite-stage sentences; Stacks Project, Tags 03EK, 04TT and 0GMX.
(blueprint: lem-pur-signed-line-scalar-tensor-tower)

The coefficient and module universe is `max uC vC u`, so slice internal Homs stay in that
universe without equating the site's object and morphism universes. The scalar-extension
API puts the scalar first: `scalarExtensionSection α M U s x` denotes `x tensor s` in the
right-scalar convention of the node. Normalizations below refer to actual sheafified tensors.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.all false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

noncomputable local instance
    {D : Type uC} [Category.{vC} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {R : Sheaf K CommRingCat.{u}}
    (M : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))
    {U V : Dᵒᵖ} (f : U ⟶ V) :
    SMul (R.obj.obj V)
      ((ModuleCat.restrictScalars
        (((sheafCompose K (forget₂ CommRingCat RingCat)).obj R).obj.map f).hom).obj
          (M.val.obj V)) :=
  (M.val.obj V).isModule.toSMul

private theorem linearEquiv_basis_bijective
    {A : Type u} [Ring A] {M : Type vC} [AddCommGroup M] [Module A M]
    (q : M ≃ₗ[A] A) (x : M) (hx : q x = 1) :
    Function.Bijective (fun r : A ↦ r • x) := by
  have hc (r : A) : q (r • x) = r := by
    rw [q.map_smul, hx, smul_eq_mul, mul_one]
  constructor
  · intro r t h
    exact (hc r).symm.trans ((congrArg q h).trans (hc t))
  · intro z
    refine ⟨q z, q.injective ?_⟩
    exact hc _

private noncomputable def presheafBasisChart
    {D : Type uC} [Category.{vC} D] {P : Dᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} P) (e : ∀ W, M.obj W)
    (he : ∀ W, Function.Bijective (fun r : P.obj W ↦ r • e W))
    (hn : ∀ {W V} (f : W ⟶ V), M.map f (e W) = e V) :
    PresheafOfModules.unit P ≅ M :=
  PresheafOfModules.isoMk
    (fun W ↦ (LinearEquiv.ofBijective
      { toFun := fun r ↦ r • e W
        map_add' := fun r t ↦ add_smul r t _
        map_smul' := fun r t ↦ mul_smul r t _ } (he W)).toModuleIso)
    (by
      intro W V f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      change P.obj W at r
      change (P.map f r) • e V = M.map f (r • e W)
      rw [M.map_smul, hn])

set_option linter.unusedSectionVars false
section CoefficientUniverses

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [UnivLE.{max uC vC, u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [hSliceSheafify : ∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

set_option allowUnsafeReducibility true in
attribute [local reducible] sheafCompose ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' SheafOfModules.unit PresheafOfModules.unit
  scalarTensorPower PresheafOfModules.restrictOver
  Functor.sheafPushforwardContinuous SheafOfModules.overFunctor
  SheafOfModules.pushforward PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj Over.forget

attribute [local irreducible] siteSheafTensorRight siteSheafTensorTmul
  siteSheafTensorSecondMap scalarExtensionDualMap changeOfRingsOfUniverses
  changeOfRingsHomOfUniverses scalarExtensionLift scalarExtensionSection

omit [UnivLE.{max uC vC, u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem signedBinaryIso_hom
    {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (M N : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (scalarTensorBinaryIso α M N).hom = scalarTensorBinaryForward α M N := rfl

attribute [local irreducible] scalarTensorBinaryIso scalarTensorBinaryForward
  scalarTensorBinaryInverse scalarTensorLeftUnitor scalarExtensionUnitIso
  scalarExtensionTowerForward scalarExtensionTowerReverse

omit [UnivLE.{max uC vC, u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem signedIso_trans_apply
    {R : Sheaf J RingCat.{u}} {M N P : SheafOfModules.{u} R}
    (e : M ≅ N) (f : N ≅ P) (W : Cᵒᵖ) (x : M.val.obj W) :
    (e ≪≫ f).hom.val.app W x = f.hom.val.app W (e.hom.val.app W x) := rfl

omit [UnivLE.{max uC vC, u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem signedIso_basis_bijective
    {R : Sheaf J CommRingCat.{u}}
    {M : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (q : M ≅ unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (W : Cᵒᵖ) (x : M.val.obj W)
    (hx : q.hom.val.app W x = (1 : R.obj.obj W)) :
    Function.Bijective (fun r : R.obj.obj W ↦ r • x) := by
  exact linearEquiv_basis_bijective
    (((evaluation _ W).mapIso q).toLinearEquiv) x hx

omit [UnivLE.{max uC vC, u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private noncomputable def tensorSecondIso
    {R : Sheaf J CommRingCat.{u}}
    (M : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {N P : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} (e : N ≅ P) :
    (siteSheafTensorRight N).obj M ≅ (siteSheafTensorRight P).obj M where
  hom := siteSheafTensorSecondMap M e.hom
  inv := siteSheafTensorSecondMap M e.inv
  hom_inv_id := by
    apply scalarTensor_hom_ext _ _
    intro U x y
    simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
      scalarTensor_second_tmul]
    have h := congrArg (fun f ↦ f.val.app U y) e.hom_inv_id
    change e.inv.val.app U (e.hom.val.app U y) = y at h
    rw [h]
    rfl
  inv_hom_id := by
    apply scalarTensor_hom_ext _ _
    intro U x y
    simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
      scalarTensor_second_tmul]
    have h := congrArg (fun f ↦ f.val.app U y) e.inv_hom_id
    change e.hom.val.app U (e.inv.val.app U y) = y at h
    rw [h]
    rfl

omit [UnivLE.{max uC vC, u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem tensorSecondIso_hom
    {R : Sheaf J CommRingCat.{u}}
    (M : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {N P : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} (e : N ≅ P) :
    (tensorSecondIso.{uC, vC, u} M e).hom = siteSheafTensorSecondMap M e.hom := rfl

attribute [local irreducible] tensorSecondIso

omit [UnivLE.{max uC vC, u}] in
private theorem power_over_unit
    {R : Sheaf J CommRingCat.{u}}
    (L : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : C) (e : L.over U ≅
      unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) :
    ∀ n : ℕ, Nonempty ((scalarTensorPower R L n).over U ≅
      unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨Iso.refl _⟩
  | one => exact ⟨e⟩
  | more n ih ih' =>
    obtain ⟨c, hc⟩ := exists_localizedSiteTensorRestriction J R U
    exact ⟨c (scalarTensorPower R L (n + 1)) L ≪≫
      (siteSheafTensorRight (A := R.over U) (L.over U)).mapIso ih'.some ≪≫
      tensorSecondIso.{max uC vC, vC, u} (R := R.over U) _ e ≪≫ scalarTensorLeftUnitor (R.over U) _⟩

omit [UnivLE.{max uC vC, u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private noncomputable def positiveComparisonSucc
    {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (L : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (K : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (b : changeOfRingsOfUniverses α L ≅ K) :
    ∀ n : ℕ, changeOfRingsOfUniverses α (scalarTensorPower R L (n + 1)) ≅
      scalarTensorPower S K (n + 1)
  | 0 => b
  | n + 1 => scalarTensorBinaryIso α (scalarTensorPower R L (n + 1)) L ≪≫
      (siteSheafTensorRight (changeOfRingsOfUniverses α L)).mapIso
        (positiveComparisonSucc α L K b n) ≪≫
      tensorSecondIso.{uC, vC, u} (scalarTensorPower S K (n + 1)) b

private noncomputable def positiveComparison
    {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (L : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (K : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (b : changeOfRingsOfUniverses α L ≅ K) :
    ∀ n : ℕ, changeOfRingsOfUniverses α (scalarTensorPower R L n) ≅
      scalarTensorPower S K n
  | 0 => scalarExtensionUnitIso α
  | n + 1 => positiveComparisonSucc α L K b n

private theorem positiveComparison_tmul
    {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (L : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (K : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (b : changeOfRingsOfUniverses α L ≅ K) (n : ℕ) (U : Cᵒᵖ) (s : S.obj.obj U)
    (x : (scalarTensorPower R L (n + 1)).val.obj U) (y : L.val.obj U) :
    (positiveComparison.{uC, vC, u} α L K b (n + 2)).hom.val.app U
      (scalarExtensionSection α (scalarTensorPower R L (n + 2)) U s
        (siteSheafTensorTmul (scalarTensorPower R L (n + 1)) L U x y)) =
      siteSheafTensorTmul (scalarTensorPower S K (n + 1)) K U
        ((positiveComparison.{uC, vC, u} α L K b (n + 1)).hom.val.app U
          (scalarExtensionSection α (scalarTensorPower R L (n + 1)) U s x))
        (b.hom.val.app U (scalarExtensionSection α L U 1 y)) := by
  change (tensorSecondIso.{uC, vC, u} _ b).hom.val.app U
    (((siteSheafTensorRight _).map (positiveComparison.{uC, vC, u} α L K b (n + 1)).hom).val.app U
      ((scalarTensorBinaryIso α (scalarTensorPower R L (n + 1)) L).hom.val.app U
        (scalarExtensionSection α (scalarTensorPower R L (n + 2)) U s
          (siteSheafTensorTmul (scalarTensorPower R L (n + 1)) L U x y)))) = _
  rw [tensorSecondIso_hom.{uC, vC, u}]
  change (siteSheafTensorSecondMap _ b.hom).val.app U
    (((siteSheafTensorRight _).map (positiveComparison.{uC, vC, u} α L K b (n + 1)).hom).val.app U
      ((scalarTensorBinaryIso α (scalarTensorPower R L (n + 1)) L).hom.val.app U
        (scalarExtensionSection α (scalarTensorPower R L (n + 2)) U s
          (siteSheafTensorTmul (scalarTensorPower R L (n + 1)) L U x y)))) = _
  erw [signedBinaryIso_hom.{uC, vC, u}, scalarTensorBinaryForward_tmul,
    scalarTensor_first_tmul, scalarTensor_second_tmul]

omit [UnivLE.{max uC vC, u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem basisFunctional_ext
    {R : Sheaf J CommRingCat.{u}}
    (M : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (e : M.val.obj U)
    (he : ∀ W : (Over U.unop)ᵒᵖ, Function.Bijective
      (fun r : R.obj.obj (op W.unop.left) ↦ r • M.val.map W.unop.hom.op e))
    (φ ψ : (M.over U.unop).val ⟶
      (unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U.unop)).val)
    (h : ∀ W : (Over U.unop)ᵒᵖ,
      φ.app W (M.val.map W.unop.hom.op e) = ψ.app W (M.val.map W.unop.hom.op e)) :
    φ = ψ := by
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply DFunLike.ext
  intro x
  obtain ⟨r, hr⟩ := (he W).2 x
  let fW : M.val.obj (op W.unop.left) →ₗ[R.obj.obj (op W.unop.left)]
      R.obj.obj (op W.unop.left) := (φ.app W).hom
  let gW : M.val.obj (op W.unop.left) →ₗ[R.obj.obj (op W.unop.left)]
      R.obj.obj (op W.unop.left) := (ψ.app W).hom
  change fW x = gW x
  rw [← hr, fW.map_smul, gW.map_smul]
  exact congrArg (fun z ↦ r • z) (h W)

omit [UnivLE.{max uC vC, u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private noncomputable def basisChart
    {R : Sheaf J CommRingCat.{u}}
    (M : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (e : M.val.obj U)
    (he : ∀ W : (Over U.unop)ᵒᵖ, Function.Bijective
      (fun r : R.obj.obj (op W.unop.left) ↦ r • M.val.map W.unop.hom.op e)) :
    unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U.unop) ≅
      M.over U.unop :=
  let q := presheafBasisChart (M.over U.unop).val
    (fun W ↦ M.val.map W.unop.hom.op e) he (by
      intro W V f
      change M.val.map f.unop.left.op (M.val.map W.unop.hom.op e) =
        M.val.map V.unop.hom.op e
      rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w])
  { hom := ⟨q.hom⟩
    inv := ⟨q.inv⟩
    hom_inv_id := SheafOfModules.hom_ext q.hom_inv_id
    inv_hom_id := SheafOfModules.hom_ext q.inv_hom_id }

omit [UnivLE.{max uC vC, u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem basisChart_apply
    {R : Sheaf J CommRingCat.{u}}
    (M : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (e : M.val.obj U)
    (he : ∀ W : (Over U.unop)ᵒᵖ, Function.Bijective
      (fun r : R.obj.obj (op W.unop.left) ↦ r • M.val.map W.unop.hom.op e))
    (W : (Over U.unop)ᵒᵖ) (r : R.obj.obj (op W.unop.left)) :
    (basisChart.{uC, vC, u} M U e he).hom.val.app W r = r • M.val.map W.unop.hom.op e := rfl

attribute [local irreducible] basisChart

omit [UnivLE.{max uC vC, u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem basisChart_inv_apply
    {R : Sheaf J CommRingCat.{u}}
    (M : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (e : M.val.obj U)
    (he : ∀ W : (Over U.unop)ᵒᵖ, Function.Bijective
      (fun r : R.obj.obj (op W.unop.left) ↦ r • M.val.map W.unop.hom.op e))
    (W : (Over U.unop)ᵒᵖ) (r : R.obj.obj (op W.unop.left)) :
    (basisChart.{uC, vC, u} M U e he).inv.val.app W (r • M.val.map W.unop.hom.op e) = r := by
  have h := congrArg (fun f ↦ f.val.app W r)
    (basisChart.{uC, vC, u} M U e he).hom_inv_id
  change (basisChart.{uC, vC, u} M U e he).inv.val.app W
    ((basisChart.{uC, vC, u} M U e he).hom.val.app W r) = r at h
  rw [basisChart_apply.{uC, vC, u}] at h
  exact h

omit [UnivLE.{max uC vC, u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private noncomputable def tensorUnitChart
    {R : Sheaf J CommRingCat.{u}}
    {M N : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (q : M ≅ unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (r : N ≅ unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (siteSheafTensorRight N).obj M ≅
      unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  (siteSheafTensorRight N).mapIso q ≪≫ tensorSecondIso.{uC, vC, u} _ r ≪≫
    scalarTensorLeftUnitor R (unit _)

omit [UnivLE.{max uC vC, u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem tensorUnitChart_tmul
    {R : Sheaf J CommRingCat.{u}}
    {M N : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (q : M ≅ unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (r : N ≅ unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (W : Cᵒᵖ) (x : M.val.obj W) (y : N.val.obj W) :
    (tensorUnitChart.{uC, vC, u} q r).hom.val.app W (siteSheafTensorTmul M N W x y) =
      q.hom.val.app W x * r.hom.val.app W y := by
  dsimp only [tensorUnitChart]
  rw [signedIso_trans_apply.{uC, vC, u}, signedIso_trans_apply.{uC, vC, u},
    tensorSecondIso_hom.{uC, vC, u}]
  simp only [Functor.mapIso_hom]
  rw [scalarTensor_first_tmul, scalarTensor_second_tmul, scalarTensorLeftUnitor_tmul]
  rfl

attribute [local irreducible] tensorUnitChart

private theorem tensorBasis_bijective
    {R : Sheaf J CommRingCat.{u}}
    (M N : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (e : M.val.obj U) (f : N.val.obj U)
    (he : ∀ W : (Over U.unop)ᵒᵖ, Function.Bijective
      (fun r : R.obj.obj (op W.unop.left) ↦ r • M.val.map W.unop.hom.op e))
    (hf : ∀ W : (Over U.unop)ᵒᵖ, Function.Bijective
      (fun r : R.obj.obj (op W.unop.left) ↦ r • N.val.map W.unop.hom.op f))
    (W : (Over U.unop)ᵒᵖ) : Function.Bijective
      (fun r : R.obj.obj (op W.unop.left) ↦
        r • ((siteSheafTensorRight N).obj M).val.map W.unop.hom.op
          (siteSheafTensorTmul M N U e f)) := by
  obtain ⟨c, _, hc⟩ := exists_localizedSiteTensorRestriction J R U.unop
  let q : ((siteSheafTensorRight N).obj M).over U.unop ≅
      unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U.unop) :=
    c M N ≪≫ tensorUnitChart.{max uC vC, vC, u} (R := R.over U.unop)
      (basisChart.{uC, vC, u} M U e he).symm (basisChart.{uC, vC, u} N U f hf).symm
  have hm : (basisChart.{uC, vC, u} M U e he).inv.val.app W
      (M.val.map W.unop.hom.op e) = (1 : R.obj.obj (op W.unop.left)) := by
    simpa only [one_smul] using (basisChart_inv_apply.{uC, vC, u} M U e he W 1)
  have hn : (basisChart.{uC, vC, u} N U f hf).inv.val.app W
      (N.val.map W.unop.hom.op f) = (1 : R.obj.obj (op W.unop.left)) := by
    simpa only [one_smul] using (basisChart_inv_apply.{uC, vC, u} N U f hf W 1)
  have hq : q.hom.val.app W
      (((siteSheafTensorRight N).obj M).val.map W.unop.hom.op
        (siteSheafTensorTmul M N U e f)) = (1 : R.obj.obj (op W.unop.left)) := by
    rw [scalarTensorTmul_naturality]
    dsimp only [q]
    rw [signedIso_trans_apply.{max uC vC, vC, u}, hc M N W.unop]
    have ht := tensorUnitChart_tmul.{max uC vC, vC, u} (R := R.over U.unop)
      (basisChart.{uC, vC, u} M U e he).symm (basisChart.{uC, vC, u} N U f hf).symm W
      (M.val.map W.unop.hom.op e) (N.val.map W.unop.hom.op f)
    have hr : (basisChart.{uC, vC, u} M U e he).inv.val.app W
        (M.val.map W.unop.hom.op e) *
      (basisChart.{uC, vC, u} N U f hf).inv.val.app W
        (N.val.map W.unop.hom.op f) = (1 : R.obj.obj (op W.unop.left)) := by
      rw [hm, hn, one_mul]
    exact ht.trans hr
  exact signedIso_basis_bijective.{max uC vC, vC, u} (R := R.over U.unop) q W _ hq

omit [UnivLE.{max uC vC, u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem dualPrecomp_isIso
    {R : Sheaf J CommRingCat.{u}}
    {M N : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} (p : M ≅ N) :
    IsIso (homObjMap p.inv (𝟙 (unit _))) := by
  have h : IsIso (((homFunctor R).mapIso p.symm.op).app (unit _)).hom := inferInstance
  exact h

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
private noncomputable def dualBasis
    {R : Sheaf J CommRingCat.{u}}
    (M : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (e : M.val.obj U)
    (he : ∀ W : (Over U.unop)ᵒᵖ, Function.Bijective
      (fun r : R.obj.obj (op W.unop.left) ↦ r • M.val.map W.unop.hom.op e)) :
    (homObj M (unit _)).val.obj U :=
  localDual M (basisChart.{uC, vC, u} M U e he).symm

attribute [local irreducible] dualBasis

end CoefficientUniverses

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC u} RingCat.{max uC vC u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  [HasWeakSheafify J AddCommGrpCat.{max uC vC u}]

/-- The node's signed powers, with the existing tensor powers and slice sheaf Hom.
Source: blueprint prop-weil-twist-preserves.proof.md; Stacks 03EK and 04TT.
(blueprint: lem-pur-signed-line-scalar-tensor-tower) -/
noncomputable def signedLinePower {R : Sheaf J CommRingCat.{max uC vC u}}
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ℤ → ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  | .ofNat n => scalarTensorPower R L n
  | .negSucc n => homObj (scalarTensorPower R L (n + 1))
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

/-- Local signed basis normalization: a genuine basis after every restriction, positive
powers by tensors, and negative powers dual to the positive ones on every slice object.
Source: Stacks 03EK and 04TT, local rank-one coordinates.
(blueprint: lem-pur-signed-line-scalar-tensor-tower) -/
def SignedLineBasisPowers {R : Sheaf J CommRingCat.{max uC vC u}}
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ)
    (e : ∀ m : ℤ, (signedLinePower.{uC, vC, u} L m).val.obj U) : Prop :=
  (∀ (m : ℤ) (W : (Over U.unop)ᵒᵖ), Function.Bijective
    (fun r : R.obj.obj (op W.unop.left) =>
      r • (signedLinePower.{uC, vC, u} L m).val.map W.unop.hom.op (e m))) ∧
  e 0 = (1 : R.obj.obj U) ∧
  (∀ n : ℕ, e (.ofNat (n + 2)) =
    siteSheafTensorTmul (scalarTensorPower R L (n + 1)) L U (e (.ofNat (n + 1))) (e 1)) ∧
  (∀ (n : ℕ) (W : (Over U.unop)ᵒᵖ),
    (e (.negSucc n)).app W
      ((scalarTensorPower R L (n + 1)).val.map W.unop.hom.op (e (.ofNat (n + 1)))) =
      (1 : R.obj.obj (op W.unop.left)))

/-- Normalization of the signed extension of the given exponent-one comparison.
The negative formula is the actual dual map followed by precomposition with the inverse
positive comparison. Source: Stacks 0GMX and 03EK.
(blueprint: lem-pur-signed-line-scalar-tensor-tower) -/
def SignedLineComparisonNormalized
    [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
    {R S : Sheaf J CommRingCat.{max uC vC u}} (α : R ⟶ S)
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (K : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (b : changeOfRingsOfUniverses α L ≅ K)
    (B : ∀ m : ℤ, changeOfRingsOfUniverses α (signedLinePower.{uC, vC, u} L m) ≅
      signedLinePower.{uC, vC, u} K m) : Prop :=
  (B 0).hom = (scalarExtensionUnitIso α).hom ∧
  (B 1).hom = b.hom ∧
  (∀ (n : ℕ) (U : Cᵒᵖ) (s : S.obj.obj U)
    (x : (scalarTensorPower R L (n + 1)).val.obj U) (y : L.val.obj U),
    (B (.ofNat (n + 2))).hom.val.app U
        (scalarExtensionSection α (scalarTensorPower R L (n + 2)) U s
          (siteSheafTensorTmul (scalarTensorPower R L (n + 1)) L U x y)) =
      siteSheafTensorTmul (scalarTensorPower S K (n + 1)) K U
        ((B (.ofNat (n + 1))).hom.val.app U
          (scalarExtensionSection α (scalarTensorPower R L (n + 1)) U s x))
        (b.hom.val.app U (scalarExtensionSection α L U 1 y))) ∧
  (∀ n : ℕ, (B (.negSucc n)).hom =
    scalarExtensionDualMap α (scalarTensorPower R L (n + 1)) ≫
      homObjMap (B (.ofNat (n + 1))).inv
        (𝟙 (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))))

variable [∀ X : C,
  (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] sheafCompose ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' SheafOfModules.unit PresheafOfModules.unit
  scalarTensorPower signedLinePower PresheafOfModules.restrictOver
  Functor.sheafPushforwardContinuous SheafOfModules.overFunctor
  SheafOfModules.pushforward PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj Over.forget

attribute [local irreducible] siteSheafTensorRight siteSheafTensorTmul
  siteSheafTensorSecondMap scalarExtensionDualMap changeOfRingsOfUniverses
  changeOfRingsHomOfUniverses scalarExtensionLift scalarExtensionSection

attribute [local irreducible] tensorSecondIso basisChart
  scalarTensorBinaryIso scalarTensorBinaryForward scalarTensorBinaryInverse
  scalarTensorLeftUnitor scalarExtensionUnitIso
  scalarExtensionTowerForward scalarExtensionTowerReverse

private theorem normalizedEvaluation_slice
    {R S : Sheaf J CommRingCat.{max uC vC u}} (α : R ⟶ S)
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (K : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (b : changeOfRingsOfUniverses α L ≅ K)
    (B : ∀ m : ℤ, changeOfRingsOfUniverses α (signedLinePower.{uC, vC, u} L m) ≅
      signedLinePower.{uC, vC, u} K m)
    (hB : SignedLineComparisonNormalized.{uC, vC, u} α L K b B)
    (n : ℕ) (U : Cᵒᵖ) (s : S.obj.obj U)
    (φ : (signedLinePower.{uC, vC, u} L (.negSucc n)).val.obj U)
    (W : (Over U.unop)ᵒᵖ) (t : S.obj.obj (op W.unop.left))
    (x : (scalarTensorPower R L (n + 1)).val.obj (op W.unop.left)) :
    ((B (.negSucc n)).hom.val.app U
      (scalarExtensionSection α _ U s φ)).app W
        ((B (.ofNat (n + 1))).hom.val.app (op W.unop.left)
          (scalarExtensionSection α _ (op W.unop.left) t x)) =
      S.obj.map W.unop.hom.op s * t *
        α.hom.app (op W.unop.left) (φ.app W x) := by
  rw [hB.2.2.2 n]
  change ((scalarExtensionDualMap α (scalarTensorPower R L (n + 1))).val.app U
    (scalarExtensionSection α _ U s φ)).app W
      ((B (.ofNat (n + 1))).inv.val.app (op W.unop.left)
        ((B (.ofNat (n + 1))).hom.val.app (op W.unop.left)
          (scalarExtensionSection α _ (op W.unop.left) t x))) = _
  have hi := congrArg (fun f ↦ f.val.app (op W.unop.left)
    (scalarExtensionSection α _ (op W.unop.left) t x))
      (B (.ofNat (n + 1))).hom_inv_id
  change (B (.ofNat (n + 1))).inv.val.app (op W.unop.left)
    ((B (.ofNat (n + 1))).hom.val.app (op W.unop.left)
      (scalarExtensionSection α _ (op W.unop.left) t x)) =
      scalarExtensionSection α (scalarTensorPower R L (n + 1)) (op W.unop.left) t x at hi
  rw [hi]
  erw [scalarExtensionDualMap_tmul_slice]

private theorem normalizedEvaluation
    {R S : Sheaf J CommRingCat.{max uC vC u}} (α : R ⟶ S)
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (K : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (b : changeOfRingsOfUniverses α L ≅ K)
    (B : ∀ m : ℤ, changeOfRingsOfUniverses α (signedLinePower.{uC, vC, u} L m) ≅
      signedLinePower.{uC, vC, u} K m)
    (hB : SignedLineComparisonNormalized.{uC, vC, u} α L K b B)
    (n : ℕ) (U : Cᵒᵖ) (s t : S.obj.obj U)
    (φ : (signedLinePower.{uC, vC, u} L (.negSucc n)).val.obj U)
    (x : (scalarTensorPower R L (n + 1)).val.obj U) :
    ((B (.negSucc n)).hom.val.app U
      (scalarExtensionSection α (signedLinePower.{uC, vC, u} L (.negSucc n)) U s φ)).app
        (op (Over.mk (𝟙 U.unop)))
          ((B (.ofNat (n + 1))).hom.val.app U
            (scalarExtensionSection α (scalarTensorPower R L (n + 1)) U t x)) =
      α.hom.app U (φ.app (op (Over.mk (𝟙 U.unop))) x) * s * t := by
  have h := normalizedEvaluation_slice.{uC, vC, u} α L K b B hB n U s φ
    (op (Over.mk (𝟙 U.unop))) t x
  simp only [Over.mk_hom] at h
  erw [S.obj.map_id] at h
  refine h.trans ?_
  change s * t * α.hom.app U (φ.app (op (Over.mk (𝟙 U.unop))) x) =
    α.hom.app U (φ.app (op (Over.mk (𝟙 U.unop))) x) * s * t
  ac_rfl

omit [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}] in
private theorem scalarMap_basis_coeff
    {R S : Sheaf J CommRingCat.{max uC vC u}} (α : R ⟶ S)
    (M : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {N : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)}
    (f : changeOfRingsOfUniverses α M ⟶ N) (U : Cᵒᵖ)
    (r : R.obj.obj U) (s : S.obj.obj U) (x : M.val.obj U) :
    f.val.app U (scalarExtensionSection α M U s (r • x)) =
      (α.hom.app U r * s) • f.val.app U (scalarExtensionSection α M U 1 x) := by
  rw [scalarExtensionSection_base_smul]
  have h := scalarExtensionSection_smul α M U (s * α.hom.app U r) 1 x
  rw [mul_one] at h
  rw [← h, map_smul, mul_comm s]

private theorem normalized_on_basis
    {R S : Sheaf J CommRingCat.{max uC vC u}} (α : R ⟶ S)
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (K : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (b : changeOfRingsOfUniverses α L ≅ K)
    (B : ∀ m : ℤ, changeOfRingsOfUniverses α (signedLinePower.{uC, vC, u} L m) ≅
      signedLinePower.{uC, vC, u} K m)
    (hB : SignedLineComparisonNormalized.{uC, vC, u} α L K b B)
    (U : Cᵒᵖ) (e : ∀ m : ℤ, (signedLinePower.{uC, vC, u} L m).val.obj U)
    (f : ∀ m : ℤ, (signedLinePower.{uC, vC, u} K m).val.obj U)
    (he : SignedLineBasisPowers.{uC, vC, u} L U e) (hf : SignedLineBasisPowers.{uC, vC, u} K U f)
    (hb : b.hom.val.app U (scalarExtensionSection α L U 1 (e 1)) = f 1) :
    ∀ m : ℤ, (B m).hom.val.app U
      (scalarExtensionSection α (signedLinePower.{uC, vC, u} L m) U 1 (e m)) = f m := by
  have hp : ∀ n : ℕ, (B (.ofNat n)).hom.val.app U
      (scalarExtensionSection α (scalarTensorPower R L n) U 1 (e (.ofNat n))) =
        f (.ofNat n) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero =>
      have hh := congrArg (fun g ↦ g.val.app U
        (scalarExtensionSection α (scalarTensorPower R L 0) U 1 (e 0))) hB.1
      refine hh.trans ?_
      change (scalarExtensionUnitIso α).hom.val.app U
        (scalarExtensionSection α (unit _) U 1 (e 0)) = _
      erw [he.2.1, scalarExtensionUnitIso_tmul, map_one, one_mul]
      exact hf.2.1.symm
    | one =>
      exact (congrArg (fun g ↦ g.val.app U
        (scalarExtensionSection α L U 1 (e 1))) hB.2.1).trans hb
    | more n _ ih =>
      rw [he.2.2.1 n]
      have hh := hB.2.2.1 n U 1 (e (.ofNat (n + 1))) (e 1)
      exact hh.trans (by rw [ih, hb, hf.2.2.1 n])
  intro m
  cases m with
  | ofNat n => exact hp n
  | negSucc n =>
    apply basisFunctional_ext.{uC, vC, max uC vC u}
      (scalarTensorPower S K (n + 1)) U (f (.ofNat (n + 1))) (hf.1 (.ofNat (n + 1)))
    intro W
    have hn := PresheafOfModules.naturality_apply (B (.ofNat (n + 1))).hom.val
      W.unop.hom.op
      (scalarExtensionSection α (scalarTensorPower R L (n + 1)) U 1
        (e (.ofNat (n + 1))))
    rw [scalarExtensionSection_naturality, map_one, hp] at hn
    have hv := normalizedEvaluation_slice.{uC, vC, u} α L K b B hB n U 1
      (e (.negSucc n)) W 1
      ((scalarTensorPower R L (n + 1)).val.map W.unop.hom.op (e (.ofNat (n + 1))))
    rw [hn, he.2.2.2 n W, map_one, map_one, one_mul, one_mul] at hv
    exact hv.trans (hf.2.2.2 n W).symm

/-- Dual scalar comparison on every positive power of a line is invertible.
Source: Stacks 0GMX, specialized using 04TT and 03EK; node proof steps 1, 2 and 4.
(blueprint: lem-pur-signed-line-scalar-tensor-tower)
Proof: restrict to a trivializing cover using localized tensor restriction. The canonical
dual map sends the dual tensor basis to the functional taking the extended basis to 1.
Its inverse sends h to h(e tensor 1) times the extended dual basis. On overlaps inverses
agree because v = v f w = w. Hom cover gluing yields a global inverse. This uses no
flatness and no enough-points hypothesis. -/
theorem signedLineDual_isIso [HasFiniteLimits C]
    {R S : Sheaf J CommRingCat.{max uC vC u}} (α : R ⟶ S)
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hL : ∃ (I : Type uC) (X : I → C), J.CoversTop X ∧
      ∀ i : I, Nonempty (L.over (X i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (X i))))
    (n : ℕ) : IsIso (scalarExtensionDualMap α (scalarTensorPower R L (n + 1))) := by
  obtain ⟨I, X, hX, h⟩ := hL
  have hpow : ∀ i, Nonempty ((scalarTensorPower R L (n + 1)).over (X i) ≅
      unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (X i))) :=
    fun i ↦ power_over_unit.{uC, vC, max uC vC u} L (X i) (h i).some (n + 1)
  have : (scalarTensorPower R L (n + 1)).IsInvertible :=
    isInvertible_of_forall_over_unit (M := scalarTensorPower R L (n + 1))
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) X hX hpow
  exact (scalarExtensionDual_localIsomorphism.{uC, vC, max uC vC u} R S α
    (scalarTensorPower R L (n + 1))).2

attribute [local irreducible] positiveComparison

private theorem negativeComparison_isIso [HasFiniteLimits C]
    {R S : Sheaf J CommRingCat.{max uC vC u}} (α : R ⟶ S)
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (K : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (hL : ∃ (I : Type uC) (X : I → C), J.CoversTop X ∧
      ∀ i : I, Nonempty (L.over (X i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (X i))))
    (b : changeOfRingsOfUniverses α L ≅ K) (n : ℕ) :
    IsIso (scalarExtensionDualMap α (scalarTensorPower R L (n + 1)) ≫
      homObjMap (positiveComparison.{uC, vC, max uC vC u} α L K b (n + 1)).inv
        (𝟙 (unit _))) := by
  have := signedLineDual_isIso.{uC, vC, u} α L hL n
  have := dualPrecomp_isIso.{uC, vC, max uC vC u}
    (positiveComparison.{uC, vC, max uC vC u} α L K b (n + 1))
  infer_instance

private noncomputable def signedComparison [HasFiniteLimits C]
    {R S : Sheaf J CommRingCat.{max uC vC u}} (α : R ⟶ S)
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (K : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (hL : ∃ (I : Type uC) (X : I → C), J.CoversTop X ∧
      ∀ i : I, Nonempty (L.over (X i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (X i))))
    (b : changeOfRingsOfUniverses α L ≅ K) :
    ∀ m : ℤ, changeOfRingsOfUniverses α (signedLinePower.{uC, vC, u} L m) ≅
      signedLinePower.{uC, vC, u} K m
  | .ofNat n => positiveComparison.{uC, vC, max uC vC u} α L K b n
  | .negSucc n =>
    haveI := negativeComparison_isIso.{uC, vC, u} α L K hL b n
    asIso (scalarExtensionDualMap α (scalarTensorPower R L (n + 1)) ≫
      homObjMap (positiveComparison.{uC, vC, max uC vC u} α L K b (n + 1)).inv
        (𝟙 (unit _)))

private theorem signedComparison_normalized [HasFiniteLimits C]
    {R S : Sheaf J CommRingCat.{max uC vC u}} (α : R ⟶ S)
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (K : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (hL : ∃ (I : Type uC) (X : I → C), J.CoversTop X ∧
      ∀ i : I, Nonempty (L.over (X i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (X i))))
    (b : changeOfRingsOfUniverses α L ≅ K) :
    SignedLineComparisonNormalized.{uC, vC, u} α L K b
      (signedComparison.{uC, vC, u} α L K hL b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (positiveComparison.{uC, vC, max uC vC u} α L K b 0).hom =
      (scalarExtensionUnitIso α).hom
    unfold positiveComparison
    rfl
  · change (positiveComparison.{uC, vC, max uC vC u} α L K b 1).hom = b.hom
    unfold positiveComparison
    rfl
  · exact positiveComparison_tmul.{uC, vC, max uC vC u} α L K b
  · intro n
    rfl

/-- Existence of all signed comparison isomorphisms, with the precise evaluation and
local coordinate formulas. Source: Stacks 0GMX, 03EK and 04TT, node proof steps 1--5.
(blueprint: lem-pur-signed-line-scalar-tensor-tower)
Proof: start with the scalar unit and b. Iterate the normalized binary scalar comparison
and tensor b to obtain the positive maps. For negative degrees compose the dual comparison,
which is invertible by the preceding line argument, with precomposition by the inverse
positive map. Evaluation cancels this inverse and gives alpha(phi(x)) s t. In compatible
bases positive induction and the dual evaluation formula give alpha(r) s in every degree.
All equalities descend from the cover by Hom gluing. -/
theorem exists_signedLineComparison [HasFiniteLimits C]
    {R S : Sheaf J CommRingCat.{max uC vC u}} (α : R ⟶ S)
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (K : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (hL : ∃ (I : Type uC) (X : I → C), J.CoversTop X ∧
      ∀ i : I, Nonempty (L.over (X i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (X i))))
    (hK : ∃ (I : Type uC) (X : I → C), J.CoversTop X ∧
      ∀ i : I, Nonempty (K.over (X i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).over (X i))))
    (b : changeOfRingsOfUniverses α L ≅ K) :
    ∃ B : ∀ m : ℤ, changeOfRingsOfUniverses α (signedLinePower.{uC, vC, u} L m) ≅
      signedLinePower.{uC, vC, u} K m,
      SignedLineComparisonNormalized.{uC, vC, u} α L K b B ∧
      (∀ (n : ℕ) (U : Cᵒᵖ) (s t : S.obj.obj U)
        (φ : (signedLinePower.{uC, vC, u} L (.negSucc n)).val.obj U)
        (x : (scalarTensorPower R L (n + 1)).val.obj U),
        ((B (.negSucc n)).hom.val.app U
          (scalarExtensionSection α (signedLinePower.{uC, vC, u} L (.negSucc n)) U s φ)).app
            (op (Over.mk (𝟙 U.unop)))
              ((B (.ofNat (n + 1))).hom.val.app U
                (scalarExtensionSection α (scalarTensorPower R L (n + 1)) U t x)) =
        α.hom.app U (φ.app (op (Over.mk (𝟙 U.unop))) x) * s * t) ∧
      (∀ (U : Cᵒᵖ) (e : ∀ m : ℤ, (signedLinePower.{uC, vC, u} L m).val.obj U)
        (f : ∀ m : ℤ, (signedLinePower.{uC, vC, u} K m).val.obj U),
        SignedLineBasisPowers.{uC, vC, u} L U e → SignedLineBasisPowers.{uC, vC, u} K U f →
        b.hom.val.app U (scalarExtensionSection α L U 1 (e 1)) = f 1 →
        ∀ (m : ℤ) (r : R.obj.obj U) (s : S.obj.obj U),
          (B m).hom.val.app U
            (scalarExtensionSection α (signedLinePower.{uC, vC, u} L m) U s (r • e m)) =
            (α.hom.app U r * s) • f m) := by
  let B := signedComparison.{uC, vC, u} α L K hL b
  have _ := hK
  have hB := signedComparison_normalized.{uC, vC, u} α L K hL b
  refine ⟨B, hB, normalizedEvaluation.{uC, vC, u} α L K b B hB, ?_⟩
  intro U e f he hf hb m r s
  rw [scalarMap_basis_coeff.{uC, vC, u}]
  rw [normalized_on_basis.{uC, vC, u} α L K b B hB U e f he hf hb]

attribute [local irreducible] signedComparison

set_option allowUnsafeReducibility true in
attribute [local semireducible] scalarTensorPower signedLinePower

set_option allowUnsafeReducibility true in
attribute [local irreducible] scalarTensorPower signedLinePower

set_option allowUnsafeReducibility true in
attribute [local semireducible] scalarTensorPower signedLinePower

set_option allowUnsafeReducibility true in
attribute [local irreducible] scalarTensorPower signedLinePower

private noncomputable def signedProductChart
    {R : Sheaf J CommRingCat.{max uC vC u}}
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (E : ∀ m : ℤ, (signedLinePower.{uC, vC, u} L m).val.obj U)
    (hE : SignedLineBasisPowers.{uC, vC, u} L U E) (a b : ℤ) :
    ((siteSheafTensorRight (signedLinePower.{uC, vC, u} L b)).obj
      (signedLinePower.{uC, vC, u} L a)).over U.unop ≅
      (signedLinePower.{uC, vC, u} L (a + b)).over U.unop :=
  (basisChart.{uC, vC, max uC vC u} _ U
    (siteSheafTensorTmul _ _ U (E a) (E b))
    (tensorBasis_bijective.{uC, vC, max uC vC u} _ _ U (E a) (E b) (hE.1 a) (hE.1 b))).symm ≪≫
    basisChart.{uC, vC, max uC vC u} _ U (E (a + b)) (hE.1 (a + b))

attribute [local irreducible] signedProductChart

set_option allowUnsafeReducibility true in
attribute [local semireducible] scalarTensorPower signedLinePower

end SheafOfModules
