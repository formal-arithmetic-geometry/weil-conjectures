/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
public import Mathlib.LinearAlgebra.Dual.Defs
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement

/-! # Descent of scalar evaluation into the internal dual sheaf

Source: Stacks Project, Cohomology on Sites, Tag 08JJ, final evaluation comparison;
Modules on Sites, Tags 03CY, 0GMW, 03EL, 04TT and 03DH.
(blueprint: lem-sfb-scalar-dual-evaluation-descent).

The scalar realization is the existing change of rings of the recorded constant module
functor, transported along its existing canonical coefficient-ring isomorphism.
Generators use the two existing sheafification units. Internal Hom sections are actual
linear maps on localized sites, so quantifying over `a : T ⟶ U` records evaluation after
every restriction. No finite generation, projectivity or flatness assumption is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory Opposite
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type (max u v)) [CommRing R] (B : Sheaf J CommRingCat.{max u v})
  (α : (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of R) ⟶ B)

/-- The node's `C_B(V) = B ⊗_{R̲} V̲`, using the recorded constant module functor and
ordinary change of rings. The canonical coefficient transport is already defined in
`constantModuleHomFunctor`; no second constant module or tensor construction is made.
Source: Stacks Tags 03CY and 03EK (blueprint: lem-sfb-scalar-dual-evaluation-descent). -/
abbrev scalarConstantRealization (V : ModuleCat.{max u v} R) :
    ringedSiteModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) :=
  changeOfRingsOfUniverses.{v, u, max u v, max u v} α
    ((constantModuleHomFunctor J R).obj V)

/-- The existing change-of-rings map applied to the constant module map `f`.
Source: Stacks Tags 03CY and 03EK (blueprint: lem-sfb-scalar-dual-evaluation-descent). -/
def scalarConstantRealizationMap {V W : ModuleCat.{max u v} R} (f : V ⟶ W) :
    scalarConstantRealization J R B α V ⟶ scalarConstantRealization J R B α W :=
  changeOfRingsHomOfUniverses α ((constantModuleHomFunctor J R).obj V)
    ((constantModuleHomFunctor J R).map f)

/-- The generator `b ⊗ v` in scalar realization: first insert the constant module section,
then insert its scalar tensor using the existing change-of-rings sheafification unit.
Source: Stacks Tags 03CY and 03EK (blueprint: lem-sfb-scalar-dual-evaluation-descent). -/
def scalarConstantGenerator (V : ModuleCat.{max u v} R) (U : Cᵒᵖ)
    (b : B.obj.obj U) (x : V) : (scalarConstantRealization J R B α V).val.obj U :=
  scalarExtensionRingIsoTmul α ((constantModuleHomFunctor J R).obj V) U
    ((constantModuleHomUnit J R V).app U x) b

/-- The internal dual of the specified scalar realization, with the actual unit module
sheaf as target. Source: Stacks Tag 04TT
(blueprint: lem-sfb-scalar-dual-evaluation-descent). -/
abbrev scalarDualEvaluationTarget (V : ModuleCat.{max u v} R) :=
  homObj (R := B) (scalarConstantRealization J R B α V)
    (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))

/-- The displayed scalar evaluation formula on every localized site. The coefficient
`b` is restricted from `U` to `T`, and the Hom section is evaluated at the object
`a : T ⟶ U` of `C/U`. At `a = id`, this is precisely `bb'α(φ(v))`.
Source: Stacks Tags 04TT and 0GMW; scalar specialization of 08JJ
(blueprint: lem-sfb-scalar-dual-evaluation-descent). -/
def ScalarDualEvaluationFormula (V : ModuleCat.{max u v} R)
    (β : scalarConstantRealization J R B α (ModuleCat.of R (V →ₗ[R] R)) ⟶
      scalarDualEvaluationTarget J R B α V) : Prop :=
  ∀ (U T : C) (a : T ⟶ U) (b : B.obj.obj (op U)) (b' : B.obj.obj (op T))
    (φ : V →ₗ[R] R) (x : V),
    (((β.val.app (op U))
      (scalarConstantGenerator J R B α (ModuleCat.of R (V →ₗ[R] R)) (op U) b φ)).app
        (op (Over.mk a))) (scalarConstantGenerator J R B α V (op T) b' x) =
      B.obj.map a.op b * b' * α.hom.app (op T)
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app (op T) (φ x))

private abbrev baseRing :=
  (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of R)

private abbrev coeffRing :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj B

private def scalarExtend (M : ringedSiteModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (baseRing J R)))
    (N : ringedSiteModules.{max u v} (coeffRing J B))
    (f : M ⟶ (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N) :
    changeOfRingsOfUniverses.{v, u, max u v, max u v} α M ⟶ N :=
  scalarExtensionLift α M N f

private lemma scalarExtend_tmul
    (M : ringedSiteModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (baseRing J R)))
    (N : ringedSiteModules.{max u v} (coeffRing J B))
    (f : M ⟶ (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N)
    (U : Cᵒᵖ) (x : M.val.obj U) (b : B.obj.obj U) :
    (scalarExtend J R B α M N f).val.app U (scalarExtensionRingIsoTmul α M U x b) =
      b • (show N.val.obj U from f.val.app U x) := by
  exact scalarExtensionLift_tmul α M N f U b x

private def scalarRingUnit : (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶
    (coeffRing J B).obj :=
  toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)) ≫
    (constantModuleHomRingIso J R).hom.hom ≫
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map α).hom

private lemma scalarRingUnit_apply (U : Cᵒᵖ) (r : R) :
    (scalarRingUnit J R B α).app U r = α.hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app U r) := by
  have h := sheafComposeNatTrans_fac J (forget₂ CommRingCat RingCat)
    (sheafificationAdjunction J CommRingCat) (sheafificationAdjunction J RingCat)
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))
  exact congrArg (fun t ↦ α.hom.app U (t.app U r)) h

private def constantLift (M : ModuleCat.{max u v} R)
    (N : ringedSiteModules.{max u v} (coeffRing J B))
    (f : (siteConstantModulePresheafGeneral (C := C) R).obj M ⟶
      (PresheafOfModules.restrictScalars (scalarRingUnit J R B α)).obj N.val) :
    (constantModuleHomFunctor J R).obj M ⟶
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N := by
  let c := constantModuleHomRingIso J R
  let a := c.hom ≫ (sheafCompose J (forget₂ CommRingCat RingCat)).map α
  let g : (siteConstantModuleFunctorGeneral J R).obj M ⟶ (restrictScalars a).obj N :=
    (PresheafOfModules.sheafificationHomEquiv
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))).symm f
  refine ⟨PresheafOfModules.homMk ((SheafOfModules.toSheaf _).map g).hom ?_⟩
  intro U r x
  have hg := (g.val.app U).hom.map_smul (c.inv.hom.app U r) x
  change g.val.app U (c.inv.hom.app U r •
      (show ((siteConstantModuleFunctorGeneral J R).obj M).val.obj U from x)) =
    α.hom.app U r • (show N.val.obj U from g.val.app U x)
  change g.val.app U (c.inv.hom.app U r •
      (show ((siteConstantModuleFunctorGeneral J R).obj M).val.obj U from x)) =
    α.hom.app U (c.hom.hom.app U (c.inv.hom.app U r)) •
      (show N.val.obj U from g.val.app U x) at hg
  have hc := ConcreteCategory.congr_hom
    (congrArg (fun t ↦ t.hom.app U) c.inv_hom_id) r
  change c.hom.hom.app U (c.inv.hom.app U r) = r at hc
  rwa [hc] at hg

private lemma constantLift_unit (M : ModuleCat.{max u v} R)
    (N : ringedSiteModules.{max u v} (coeffRing J B))
    (f : (siteConstantModulePresheafGeneral (C := C) R).obj M ⟶
      (PresheafOfModules.restrictScalars (scalarRingUnit J R B α)).obj N.val)
    (U : Cᵒᵖ) (x : M) :
    (constantLift J R B α M N f).val.app U ((constantModuleHomUnit J R M).app U x) =
      f.app U x := by
  let a := (constantModuleHomRingIso J R).hom ≫
    (sheafCompose J (forget₂ CommRingCat RingCat)).map α
  have h := (PresheafOfModules.sheafificationHomEquiv.{max u v}
    (R := (constantSheaf J RingCat.{max u v}).obj (RingCat.of R))
    (F := (restrictScalars a).obj N)
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))).apply_symm_apply f
  exact congrArg (fun t ↦ t.app U (show
    ((siteConstantModulePresheafGeneral (C := C) R).obj M).obj U from x)) h

private def scalarLift (M : ModuleCat.{max u v} R)
    (N : ringedSiteModules.{max u v} (coeffRing J B))
    (f : (siteConstantModulePresheafGeneral (C := C) R).obj M ⟶
      (PresheafOfModules.restrictScalars (scalarRingUnit J R B α)).obj N.val) :
    scalarConstantRealization J R B α M ⟶ N :=
  scalarExtend J R B α _ N (constantLift J R B α M N f)

private lemma scalarLift_generator (M : ModuleCat.{max u v} R)
    (N : ringedSiteModules.{max u v} (coeffRing J B))
    (f : (siteConstantModulePresheafGeneral (C := C) R).obj M ⟶
      (PresheafOfModules.restrictScalars (scalarRingUnit J R B α)).obj N.val)
    (U : Cᵒᵖ) (b : B.obj.obj U) (x : M) :
    (scalarLift J R B α M N f).val.app U (scalarConstantGenerator J R B α M U b x) =
      b • (show N.val.obj U from f.app U x) := by
  change (scalarExtend J R B α _ N _).val.app U
    (scalarExtensionRingIsoTmul α _ U ((constantModuleHomUnit J R M).app U x) b) = _
  rw [scalarExtend_tmul, constantLift_unit]

private lemma scalarTmul_restrict
    (M : ringedSiteModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (baseRing J R)))
    {U T : Cᵒᵖ} (a : U ⟶ T) (x : M.val.obj U) (b : B.obj.obj U) :
    (changeOfRingsOfUniverses.{v, u, max u v, max u v} α M).val.map a
        (scalarExtensionRingIsoTmul α M U x b) =
      scalarExtensionRingIsoTmul α M T (M.val.map a x) (B.obj.map a b) := by
  exact scalarExtensionSection_naturality α M a b x

private lemma rawScalarOver_ext
    (M : ringedSiteModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (baseRing J R)))
    (N : ringedSiteModules.{max u v} (coeffRing J B)) (U : C)
    (f g : (PresheafOfModules.restrictOver B.obj U).obj
        (changeOfRingsOfUniverses.{v, u, max u v, max u v} α M).val ⟶
      (PresheafOfModules.restrictOver B.obj U).obj N.val)
    (h : ∀ (W : Over U) (b : B.obj.obj (op W.left)) (x : M.val.obj (op W.left)),
      f.app (op W) (scalarExtensionRingIsoTmul α M (op W.left) x b) =
        g.app (op W) (scalarExtensionRingIsoTmul α M (op W.left) x b)) : f = g := by
  let E := changeOfRingsPresheafOfUniverses.{v, u, max u v, max u v} α M
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (coeffRing J B).obj)).unit.app E
  let τ := (PresheafOfModules.toPresheaf _).map η
  have : Presheaf.IsLocallySurjective J τ :=
    inferInstanceAs (Presheaf.IsLocallySurjective J (toSheafify J E.presheaf))
  ext W s
  apply N.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J τ s)
  intro T a ha
  obtain ⟨z, hz⟩ := ha
  let W' : Over U := Over.mk (a ≫ W.unop.hom)
  have hf := PresheafOfModules.naturality_apply f
    (Over.homMk a : W' ⟶ W.unop).op s
  have hg := PresheafOfModules.naturality_apply g
    (Over.homMk a : W' ⟶ W.unop).op s
  change η.app (op T) z =
    (changeOfRingsOfUniverses.{v, u, max u v, max u v} α M).val.map a.op s at hz
  change f.app (op W') ((changeOfRingsOfUniverses.{v, u, max u v, max u v} α M).val.map a.op s) =
    N.val.map a.op (f.app W s) at hf
  change g.app (op W') ((changeOfRingsOfUniverses.{v, u, max u v, max u v} α M).val.map a.op s) =
    N.val.map a.op (g.app W s) at hg
  change N.val.map a.op (f.app W s) = N.val.map a.op (g.app W s)
  rw [← hf, ← hg, ← hz]
  have he : η.app (op T) ≫ f.app (op W') = η.app (op T) ≫ g.app (op W') := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    exact h W' 1 x
  exact ConcreteCategory.congr_hom he z

private lemma scalarOver_ext (M : ModuleCat.{max u v} R)
    (N : ringedSiteModules.{max u v} (coeffRing J B)) (U : C)
    (f g : (PresheafOfModules.restrictOver B.obj U).obj
        (scalarConstantRealization J R B α M).val ⟶
      (PresheafOfModules.restrictOver B.obj U).obj N.val)
    (h : ∀ (W : Over U) (b : B.obj.obj (op W.left)) (x : M),
      f.app (op W) (scalarConstantGenerator J R B α M (op W.left) b x) =
        g.app (op W) (scalarConstantGenerator J R B α M (op W.left) b x)) : f = g := by
  apply rawScalarOver_ext J R B α _ N U f g
  intro W b x
  let η := constantModuleHomUnit J R M
  have : Presheaf.IsLocallySurjective J η :=
    inferInstanceAs (Presheaf.IsLocallySurjective J
      (toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj M).presheaf))
  apply N.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J η x)
  intro T a ha
  obtain ⟨m, hm⟩ := ha
  let W' : Over U := Over.mk (a ≫ W.hom)
  have hf := PresheafOfModules.naturality_apply f
    (Over.homMk a : W' ⟶ W).op (scalarExtensionRingIsoTmul α _ (op W.left) x b)
  have hg := PresheafOfModules.naturality_apply g
    (Over.homMk a : W' ⟶ W).op (scalarExtensionRingIsoTmul α _ (op W.left) x b)
  change η.app (op T) m =
    ((constantModuleHomFunctor J R).obj M).val.map a.op x at hm
  change f.app (op W') ((scalarConstantRealization J R B α M).val.map a.op
      (scalarExtensionRingIsoTmul α _ (op W.left) x b)) =
    N.val.map a.op (f.app (op W) (scalarExtensionRingIsoTmul α _ (op W.left) x b)) at hf
  change g.app (op W') ((scalarConstantRealization J R B α M).val.map a.op
      (scalarExtensionRingIsoTmul α _ (op W.left) x b)) =
    N.val.map a.op (g.app (op W) (scalarExtensionRingIsoTmul α _ (op W.left) x b)) at hg
  change N.val.map a.op (f.app (op W) (scalarExtensionRingIsoTmul α _ (op W.left) x b)) =
    N.val.map a.op (g.app (op W) (scalarExtensionRingIsoTmul α _ (op W.left) x b))
  rw [← hf, ← hg]
  erw [scalarTmul_restrict, ← hm]
  exact h W' (B.obj.map a.op b) m

private lemma scalarHom_ext (M : ModuleCat.{max u v} R)
    (N : ringedSiteModules.{max u v} (coeffRing J B))
    (f g : scalarConstantRealization J R B α M ⟶ N)
    (h : ∀ (U : Cᵒᵖ) (b : B.obj.obj U) (x : M),
      f.val.app U (scalarConstantGenerator J R B α M U b x) =
        g.val.app U (scalarConstantGenerator J R B α M U b x)) : f = g := by
  ext U x
  have he := scalarOver_ext J R B α M N U.unop
    ((PresheafOfModules.restrictOver B.obj U.unop).map f.val)
    ((PresheafOfModules.restrictOver B.obj U.unop).map g.val)
    (fun W b x ↦ h (op W.left) b x)
  exact congrArg (fun t ↦ t.app (op (Over.mk (𝟙 U.unop))) x) he

private def scalarFunctionalRaw (V : ModuleCat.{max u v} R) (φ : V →ₗ[R] R) :
    (siteConstantModulePresheafGeneral (C := C) R).obj V ⟶
      (PresheafOfModules.restrictScalars (scalarRingUnit J R B α)).obj
        (unit (coeffRing J B)).val where
  app U := ModuleCat.ofHom
    (Y := ((PresheafOfModules.restrictScalars (scalarRingUnit J R B α)).obj
      (unit (coeffRing J B)).val).obj U)
    { toFun x := (scalarRingUnit J R B α).app U (φ x)
      map_add' x y := by rw [map_add, map_add]
      map_smul' r x := by
        change (scalarRingUnit J R B α).app U (φ (r • x)) =
          (scalarRingUnit J R B α).app U r * (scalarRingUnit J R B α).app U (φ x)
        rw [map_smul, smul_eq_mul, map_mul] }
  naturality {U T} a := by
    ext x
    exact NatTrans.naturality_apply (scalarRingUnit J R B α) a (φ x)

private def scalarFunctional (V : ModuleCat.{max u v} R) (φ : V →ₗ[R] R) :
    scalarConstantRealization J R B α V ⟶ unit (coeffRing J B) :=
  scalarLift J R B α V _ (scalarFunctionalRaw J R B α V φ)

private lemma scalarFunctional_generator (V : ModuleCat.{max u v} R) (φ : V →ₗ[R] R)
    (U : Cᵒᵖ) (b : B.obj.obj U) (x : V) :
    (scalarFunctional J R B α V φ).val.app U (scalarConstantGenerator J R B α V U b x) =
      b * (show B.obj.obj U from (scalarRingUnit J R B α).app U (φ x)) := by
  exact scalarLift_generator J R B α V _ (scalarFunctionalRaw J R B α V φ) U b x

private def scalarDualRaw (V : ModuleCat.{max u v} R) :
    (siteConstantModulePresheafGeneral (C := C) R).obj (ModuleCat.of R (V →ₗ[R] R)) ⟶
      (PresheafOfModules.restrictScalars (scalarRingUnit J R B α)).obj
        (scalarDualEvaluationTarget J R B α V).val where
  app U := ModuleCat.ofHom
    (Y := ((PresheafOfModules.restrictScalars (scalarRingUnit J R B α)).obj
      (scalarDualEvaluationTarget J R B α V).val).obj U)
    { toFun φ := (PresheafOfModules.restrictOver B.obj U.unop).map
        (scalarFunctional J R B α V φ).val
      map_add' φ ψ := by
        apply scalarOver_ext J R B α V (unit (coeffRing J B)) U.unop
        intro W b x
        change (scalarFunctional J R B α V (φ + ψ)).val.app _ _ =
          (scalarFunctional J R B α V φ).val.app _ _ +
            (scalarFunctional J R B α V ψ).val.app _ _
        change (scalarFunctional J R B α V (φ + ψ)).val.app (op W.left)
            (scalarConstantGenerator J R B α V (op W.left) b x) =
          (scalarFunctional J R B α V φ).val.app (op W.left)
              (scalarConstantGenerator J R B α V (op W.left) b x) +
            (scalarFunctional J R B α V ψ).val.app (op W.left)
              (scalarConstantGenerator J R B α V (op W.left) b x)
        rw [scalarFunctional_generator, scalarFunctional_generator, scalarFunctional_generator]
        change b * (show B.obj.obj (op W.left) from
          (scalarRingUnit J R B α).app _ (φ x + ψ x)) = _
        rw [map_add, mul_add]
      map_smul' r φ := by
        change (PresheafOfModules.restrictOver B.obj U.unop).map
            (scalarFunctional J R B α V (r • φ)).val =
          (show B.obj.obj (op U.unop) from (scalarRingUnit J R B α).app U r) •
            (PresheafOfModules.restrictOver B.obj U.unop).map
              (scalarFunctional J R B α V φ).val
        apply scalarOver_ext J R B α V (unit (coeffRing J B)) U.unop
        intro W b x
        change (scalarFunctional J R B α V (r • φ)).val.app (op W.left)
            (scalarConstantGenerator J R B α V (op W.left) b x) =
          B.obj.map W.hom.op ((scalarRingUnit J R B α).app U r) •
            (show (unit (coeffRing J B)).val.obj (op W.left) from
              (scalarFunctional J R B α V φ).val.app (op W.left)
                (scalarConstantGenerator J R B α V (op W.left) b x))
        rw [scalarFunctional_generator, scalarFunctional_generator]
        change b * (show B.obj.obj (op W.left) from
          (scalarRingUnit J R B α).app _ (r * φ x)) = _
        rw [map_mul]
        have hn := NatTrans.naturality_apply (scalarRingUnit J R B α) W.hom.op r
        change (scalarRingUnit J R B α).app (op W.left) r =
          B.obj.map W.hom.op ((scalarRingUnit J R B α).app U r) at hn
        rw [← hn]
        exact mul_left_comm _ _ _ }
  naturality {U T} a := by
    ext φ
    rfl

private def scalarDual (V : ModuleCat.{max u v} R) :
    scalarConstantRealization J R B α (ModuleCat.of R (V →ₗ[R] R)) ⟶
      scalarDualEvaluationTarget J R B α V :=
  scalarLift J R B α _ _ (scalarDualRaw J R B α V)

private lemma scalarDual_formula (V : ModuleCat.{max u v} R) :
    ScalarDualEvaluationFormula J R B α V (scalarDual J R B α V) := by
  intro U T a b b' φ x
  change (((scalarLift J R B α _ _ (scalarDualRaw J R B α V)).val.app _ _).app _) _ = _
  rw [scalarLift_generator]
  change B.obj.map a.op b • ((scalarFunctional J R B α V φ).val.app _
    (scalarConstantGenerator J R B α V (op T) b' x)) = _
  rw [scalarFunctional_generator, scalarRingUnit_apply]
  change B.obj.map a.op b * (b' * _) = _
  exact (mul_assoc _ _ _).symm

private lemma scalarDualHom_ext (M V : ModuleCat.{max u v} R)
    (γ γ' : scalarConstantRealization J R B α M ⟶
      scalarDualEvaluationTarget J R B α V)
    (h : ∀ (U T : C) (a : T ⟶ U) (b : B.obj.obj (op U)) (b' : B.obj.obj (op T))
      (m : M) (x : V),
      ((γ.val.app (op U) (scalarConstantGenerator J R B α M (op U) b m)).app
          (op (Over.mk a))) (scalarConstantGenerator J R B α V (op T) b' x) =
        ((γ'.val.app (op U) (scalarConstantGenerator J R B α M (op U) b m)).app
          (op (Over.mk a))) (scalarConstantGenerator J R B α V (op T) b' x)) :
    γ = γ' := by
  apply scalarHom_ext J R B α M _ γ γ'
  intro U b m
  apply scalarOver_ext J R B α V (unit (coeffRing J B)) U.unop
  intro W b' x
  exact h U.unop W.left W.hom b b' m x

private lemma scalarMap_generator {V W : ModuleCat.{max u v} R} (f : V ⟶ W)
    (U : Cᵒᵖ) (b : B.obj.obj U) (x : V) :
    (scalarConstantRealizationMap J R B α f).val.app U
      (scalarConstantGenerator J R B α V U b x) =
        scalarConstantGenerator J R B α W U b (f x) := by
  have h := scalarExtension_map_tmul α ((constantModuleHomFunctor J R).map f) U b
    ((constantModuleHomUnit J R V).app U x)
  have hn := toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map
    ((siteConstantModulePresheafGeneral (C := C) R).map f))
  have hx := (ConcreteCategory.congr_hom (congr_app hn U) x).symm
  change ((constantModuleHomFunctor J R).map f).val.app U
      ((constantModuleHomUnit J R V).app U x) =
    (constantModuleHomUnit J R W).app U (f x) at hx
  exact h.trans (congrArg (fun z ↦ scalarExtensionSection α
    ((constantModuleHomFunctor J R).obj W) U b z) hx)

/-- Scalar evaluation descends uniquely, is contravariantly natural, and admits the
stated generator test for equality. Restriction compatibility is built into the sheaf
morphisms and their internal-Hom sections; the formula explicitly evaluates on every
object of each localized site.

Source: Stacks Project, Tag 08JJ, final evaluation comparison, with the explicit
constant-scalar specialization using Tags 03CY, 0GMW, 03EL, 04TT and 03DH.
(blueprint: lem-sfb-scalar-dual-evaluation-descent).

Proof plan, following the five steps of the node:
1. Form `P_M(U) = B(U) ⊗_R M`. The module-sheafification interface and
   lem-pc-sites-module-sheafification-tensor identify its sheafification with `C_B(M)`.
   The action is B-linear by uniqueness of the extended action. The constant-restriction
   and lem-sfb-localized-site-tensor-restriction comparisons preserve these generators.
2. The raw pairing `(b ⊗ φ, b' ⊗ x) ↦ bb'α(φ(x))` is R-balanced in both factors,
   B-bilinear and compatible with restriction. Apply
   lem-pc-sites-module-sheafification-bilinear-extension to obtain its unique sheaf pairing.
3. Curry on each slice: a section `s` over `U` sends `t` over `a : T ⟶ U` to the
   pairing of `s|_T` with `t`. This gives a B-linear internal-Hom section, compatible
   with every further restriction, hence the required sheaf morphism and formula.
4. For maps from `C_B(M)` to the dual of `C_B(V)`, evaluate at identity arrows to obtain
   sheaf pairings. Equality on generators implies equality on raw tensors by additivity,
   then equality of the pairings by uniqueness of bilinear sheafification extension.
   The internal-Hom restriction rule recovers every component of the maps from these
   pairings. With `M = V*`, this proves uniqueness and the stated equality criterion.
5. For `f : V ⟶ W`, both naturality composites evaluate to `bb'α(ψ(f(x)))`.
   The preceding argument with `M = W*` gives equality as sheaf morphisms.
   These constructions require no finiteness, projectivity, flatness or exactness. -/
theorem exists_scalarDualEvaluationDescent :
    (∀ V : ModuleCat.{max u v} R,
      ∃! β : scalarConstantRealization J R B α (ModuleCat.of R (V →ₗ[R] R)) ⟶
          scalarDualEvaluationTarget J R B α V,
        ScalarDualEvaluationFormula J R B α V β) ∧
    (∀ (V W : ModuleCat.{max u v} R) (f : V ⟶ W)
      (βV : scalarConstantRealization J R B α (ModuleCat.of R (V →ₗ[R] R)) ⟶
        scalarDualEvaluationTarget J R B α V)
      (βW : scalarConstantRealization J R B α (ModuleCat.of R (W →ₗ[R] R)) ⟶
        scalarDualEvaluationTarget J R B α W),
      ScalarDualEvaluationFormula J R B α V βV →
      ScalarDualEvaluationFormula J R B α W βW →
        βW ≫ homObjMap (R := B) (scalarConstantRealizationMap J R B α f)
            (𝟙 (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))) =
          scalarConstantRealizationMap J R B α (ModuleCat.ofHom f.hom.dualMap) ≫ βV) ∧
    (∀ (V : ModuleCat.{max u v} R)
      (γ γ' : scalarConstantRealization J R B α (ModuleCat.of R (V →ₗ[R] R)) ⟶
        scalarDualEvaluationTarget J R B α V),
      (∀ (U T : C) (a : T ⟶ U) (b : B.obj.obj (op U)) (b' : B.obj.obj (op T))
        (φ : V →ₗ[R] R) (x : V),
        (((γ.val.app (op U))
          (scalarConstantGenerator J R B α (ModuleCat.of R (V →ₗ[R] R)) (op U) b φ)).app
            (op (Over.mk a))) (scalarConstantGenerator J R B α V (op T) b' x) =
        (((γ'.val.app (op U))
          (scalarConstantGenerator J R B α (ModuleCat.of R (V →ₗ[R] R)) (op U) b φ)).app
            (op (Over.mk a))) (scalarConstantGenerator J R B α V (op T) b' x)) →
        γ = γ') := by
  refine ⟨?_, ?_, ?_⟩
  · intro V
    refine ⟨scalarDual J R B α V, scalarDual_formula J R B α V, ?_⟩
    intro γ hγ
    apply scalarDualHom_ext J R B α _ V γ (scalarDual J R B α V)
    intro U T a b b' φ x
    exact (hγ U T a b b' φ x).trans
      ((scalarDual_formula J R B α V) U T a b b' φ x).symm
  · intro V W f βV βW hV hW
    apply scalarDualHom_ext J R B α _ V
    intro U T a b b' ψ x
    change ((βW.val.app (op U)
        (scalarConstantGenerator J R B α (ModuleCat.of R (W →ₗ[R] R)) (op U) b ψ)).app
        (op (Over.mk a)))
        ((scalarConstantRealizationMap J R B α f).val.app (op T)
          (scalarConstantGenerator J R B α V (op T) b' x)) =
      ((βV.val.app (op U)
        ((scalarConstantRealizationMap J R B α (ModuleCat.ofHom f.hom.dualMap)).val.app
          (op U) (scalarConstantGenerator J R B α
            (ModuleCat.of R (W →ₗ[R] R)) (op U) b ψ))).app
        (op (Over.mk a))) (scalarConstantGenerator J R B α V (op T) b' x)
    rw [scalarMap_generator, scalarMap_generator]
    exact (hW U T a b b' ψ (f x)).trans
      (hV U T a b b' (f.hom.dualMap ψ) x).symm
  · intro V γ γ' h
    exact scalarDualHom_ext J R B α _ V γ γ' h

end SheafOfModules
