/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.MeromorphicModule
public import Sheaf.RingTheory.WeaklyAssociated
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.MeromorphicGenericAffine
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.KrullDimension.Zero
import WeilConjectures.Mathlib.Topology.Sober
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-!
# Meromorphic modules as products at generic points

Source: Stacks Project, Divisors, Lemma 31.24.6 (Tag 0EMF)
(blueprint: lem-sc-meromorphic-weakass-generic-product).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def localizedScalarTensorEquiv
    {R : Type u} [CommRing R] (S : Submonoid R)
    (M : Type u) [AddCommGroup M] [Module R M] :
    LocalizedModule S R ⊗[R] M ≃ₗ[R] LocalizedModule S M :=
  TensorProduct.congr
      ((LocalizedModule.equivTensorProduct S R).restrictScalars R ≪≫ₗ
        TensorProduct.rid R (Localization S))
      (LinearEquiv.refl R M) ≪≫ₗ
    (LocalizedModule.equivTensorProduct S M).symm.restrictScalars R

private theorem localizedScalarTensorEquiv_mk
    {R : Type u} [CommRing R] (S : Submonoid R)
    (M : Type u) [AddCommGroup M] [Module R M] (a : R) (s : S) (m : M) :
    localizedScalarTensorEquiv S M (LocalizedModule.mk a s ⊗ₜ[R] m) =
      LocalizedModule.mk (a • m) s := by
  simp only [localizedScalarTensorEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, LinearEquiv.restrictScalars_apply,
    LocalizedModule.equivTensorProduct_apply_mk, LinearEquiv.refl_apply,
    TensorProduct.rid_tmul, Algebra.smul_def]
  rw [show algebraMap R (Localization S) a * Localization.mk 1 s =
      Localization.mk a s by
    rw [← Localization.mk_algebraMap (A := R) a]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, Localization.mk_mul,
      mul_one, one_mul]]
  rw [LocalizedModule.equivTensorProduct_symm_apply_tmul, LocalizedModule.smul'_mk]

attribute [local instance] presheafMonoidalCategory

private noncomputable def meromorphicPresheafTensorIso (X : Scheme.{u}) (F : X.Modules) :
    meromorphicPresheaf X (unit X) ⊗ F.val ≅ meromorphicPresheaf X F := by
  refine PresheafOfModules.isoMk (fun U ↦
    (localizedScalarTensorEquiv (meromorphicDenominators X U.unop)
      Γ(F, U.unop)).toModuleIso) ?_
  intro U V i
  cases U with | op U =>
   cases V with | op V =>
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
    | tmul a m =>
      induction a using LocalizedModule.induction_on with
      | h a b =>
        change localizedScalarTensorEquiv _ _
            (meromorphicRestriction X (unit X) i.unop (LocalizedModule.mk a b) ⊗ₜ
              F.presheaf.map i m) =
          meromorphicRestriction X F i.unop
            (localizedScalarTensorEquiv _ _ (LocalizedModule.mk a b ⊗ₜ m))
        erw [(exists_meromorphicRestriction X (unit X) i.unop).choose_spec,
          localizedScalarTensorEquiv_mk, localizedScalarTensorEquiv_mk,
          (exists_meromorphicRestriction X F i.unop).choose_spec]
        congr 1
        exact (F.val.map_smul i a m).symm

private noncomputable def meromorphicTensorIso (X : Scheme.{u}) (F : X.Modules) :
    meromorphicModule X (unit X) ⊗ F ≅ meromorphicModule X F := by
  let a := sheafification X
  letI := sheafificationMonoidal X
  exact (Iso.refl _ ⊗ᵢ
      (asIso ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).counit.app F)).symm) ≪≫
    Functor.Monoidal.μIso a _ _ ≪≫ a.mapIso (meromorphicPresheafTensorIso X F)

private theorem generic_fromSpecStalk_apply (X : Scheme.{u})
    (η : {x : X // x ∈ genericPoints X}) (y : Spec (X.presheaf.stalk η.val)) :
    X.fromSpecStalk η.val y = η.val := by
  apply mem_genericPoints_iff_forall_specializes.mp η.property
  have h : X.fromSpecStalk η.val y ∈ Set.range (X.fromSpecStalk η.val) := ⟨y, rfl⟩
  rwa [X.range_fromSpecStalk] at h

private theorem generic_stalk_spectrum_subsingleton (X : Scheme.{u})
    (η : {x : X // x ∈ genericPoints X}) :
    Subsingleton (PrimeSpectrum (X.presheaf.stalk η.val)) := by
  refine ⟨fun a b ↦ (X.fromSpecStalk η.val).isEmbedding.injective ?_⟩
  exact (generic_fromSpecStalk_apply X η a).trans
    (generic_fromSpecStalk_apply X η b).symm

private theorem generic_denominator_isUnit (X : Scheme.{u})
    (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U)
    (b : meromorphicDenominators X U) :
    IsUnit (X.presheaf.germ U η.val hη b.val) := by
  let := generic_stalk_spectrum_subsingleton X η
  let : Ring.KrullDimLE 0 (X.presheaf.stalk η.val) :=
    ⟨Order.krullDim_nonpos_of_subsingleton⟩
  apply (le_isUnit_iff_zero_notMem.mpr
    ((show (0 : X.presheaf.stalk η.val) ∉ nonZeroDivisors _ from zero_notMem_nonZeroDivisors)))
  exact (Submonoid.mem_iInf.mp b.property ⟨η.val, hη⟩)

private theorem generic_preimage_eq_bot (X : Scheme.{u})
    (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∉ U) :
    X.fromSpecStalk η.val ⁻¹ᵁ U = ⊥ := by
  ext y
  change X.fromSpecStalk η.val y ∈ U ↔ False
  rw [generic_fromSpecStalk_apply]
  exact iff_false_intro hη

private theorem generic_factor_sections_subsingleton (X : Scheme.{u})
    (η : {x : X // x ∈ genericPoints X}) (N : (Spec (X.presheaf.stalk η.val)).Modules)
    (U : X.Opens) (hη : η.val ∉ U) :
    Subsingleton Γ((pushforward (X.fromSpecStalk η.val)).obj N, U) := by
  change Subsingleton Γ(N, X.fromSpecStalk η.val ⁻¹ᵁ U)
  let : Subsingleton Γ(Spec (X.presheaf.stalk η.val), X.fromSpecStalk η.val ⁻¹ᵁ U) :=
    CommRingCat.subsingleton_of_isTerminal
    (TopCat.Sheaf.isTerminalOfEqEmpty (Spec (X.presheaf.stalk η.val)).sheaf
      (generic_preimage_eq_bot X η U hη))
  exact Module.subsingleton Γ(Spec (X.presheaf.stalk η.val),
    X.fromSpecStalk η.val ⁻¹ᵁ U) _

set_option backward.isDefEq.respectTransparency false in
private noncomputable def genericStalkSectionMap (X : Scheme.{u}) (F : X.Modules)
    (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) :
    Γ(F, U) →ₗ[Γ(X, U)]
      Γ((pushforward (X.fromSpecStalk η.val)).obj
        (tilde (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val))), U) := by
  classical
  by_cases hη : η.val ∈ U
  · exact
      { toFun := fun m ↦ tilde.toOpen
          (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val))
          (X.fromSpecStalk η.val ⁻¹ᵁ U) (F.presheaf.germ U η.val hη m)
        map_add' := fun m n ↦ by simp only [map_add]
        map_smul' := fun a m ↦ by
          rw [germ_smul]
          change (tilde.toOpen
            (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val))
            (X.fromSpecStalk η.val ⁻¹ᵁ U)).hom
              (X.presheaf.germ U η.val hη a • F.presheaf.germ U η.val hη m) = _
          rw [LinearMap.map_smul]
          change X.presheaf.germ U η.val hη a •
            (show Γ(tilde (ModuleCat.of (X.presheaf.stalk η.val)
              (F.presheaf.stalk η.val)), X.fromSpecStalk η.val ⁻¹ᵁ U) from
              tilde.toOpen _ _ (F.presheaf.germ U η.val hη m)) = _
          rw [smul_Spec_def]
          change _ = (X.fromSpecStalk η.val).app U a •
            (show Γ(tilde (ModuleCat.of (X.presheaf.stalk η.val)
              (F.presheaf.stalk η.val)), X.fromSpecStalk η.val ⁻¹ᵁ U) from
              tilde.toOpen _ _ (F.presheaf.germ U η.val hη m))
          rw [X.fromSpecStalk_app hη]
          rfl }
  · let := generic_factor_sections_subsingleton X η
      (tilde (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val))) U hη
    exact 0

private theorem genericStalkSectionMap_apply (X : Scheme.{u}) (F : X.Modules)
    (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U)
    (m : Γ(F, U)) :
    genericStalkSectionMap X F η U m =
      tilde.toOpen (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val))
        (X.fromSpecStalk η.val ⁻¹ᵁ U) (F.presheaf.germ U η.val hη m) := by
  simp only [genericStalkSectionMap, dif_pos hη]
  rfl

private theorem generic_factor_denominator_isUnit (X : Scheme.{u})
    (η : {x : X // x ∈ genericPoints X}) (N : (Spec (X.presheaf.stalk η.val)).Modules)
    (U : X.Opens) (b : meromorphicDenominators X U) :
    IsUnit (algebraMap Γ(X, U)
      (Module.End Γ(X, U) Γ((pushforward (X.fromSpecStalk η.val)).obj N, U)) b.val) := by
  classical
  by_cases hη : η.val ∈ U
  · rw [Module.End.isUnit_iff]
    change Function.Bijective (fun m : Γ((pushforward (X.fromSpecStalk η.val)).obj N, U) ↦
      b.val • m)
    change Function.Bijective (fun m : Γ(N, X.fromSpecStalk η.val ⁻¹ᵁ U) ↦
      (X.fromSpecStalk η.val).app U b.val • m)
    rw [X.fromSpecStalk_app hη]
    change Function.Bijective (fun m : Γ(N, X.fromSpecStalk η.val ⁻¹ᵁ U) ↦
      (Spec (X.presheaf.stalk η.val)).presheaf.map (homOfLE le_top).op
        ((Scheme.ΓSpecIso (X.presheaf.stalk η.val)).inv
          (X.presheaf.germ U η.val hη b.val)) • m)
    change Function.Bijective (fun m : Γ(N, X.fromSpecStalk η.val ⁻¹ᵁ U) ↦
      X.presheaf.germ U η.val hη b.val • m)
    exact (generic_denominator_isUnit X η U hη b).smul_bijective
  · let := generic_factor_sections_subsingleton X η N U hη
    rw [Module.End.isUnit_iff]
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun x ↦ ⟨x, Subsingleton.elim _ _⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem genericStalkSectionMap_natural (X : Scheme.{u}) (F : X.Modules)
    (η : {x : X // x ∈ genericPoints X}) {U V : X.Opens} (i : V ⟶ U) (m : Γ(F, U)) :
    genericStalkSectionMap X F η V (F.presheaf.map i.op m) =
      ((pushforward (X.fromSpecStalk η.val)).obj
        (tilde (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val)))).presheaf.map
        i.op (genericStalkSectionMap X F η U m) := by
  classical
  by_cases hη : η.val ∈ V
  · rw [genericStalkSectionMap_apply X F η V hη,
      genericStalkSectionMap_apply X F η U (i.le hη),
      TopCat.Presheaf.germ_res_apply]
    exact (CategoryTheory.congr_fun
      (tilde.toOpen_res
        (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val))
        _ _ ((TopologicalSpace.Opens.map (X.fromSpecStalk η.val).base).map i))
      (F.presheaf.germ U η.val (i.le hη) m)).symm
  · let := generic_factor_sections_subsingleton X η
      (tilde (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val))) V hη
    exact Subsingleton.elim _ _

private noncomputable def genericFractionMap (X : Scheme.{u}) (F : X.Modules)
    (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) :
    LocalizedModule (meromorphicDenominators X U) Γ(F, U) →ₗ[Γ(X, U)]
      Γ((pushforward (X.fromSpecStalk η.val)).obj
        (tilde (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val))), U) :=
  LocalizedModule.lift _ (genericStalkSectionMap X F η U)
    (fun b ↦ generic_factor_denominator_isUnit X η _ U b)

private theorem genericFractionMap_mk_one (X : Scheme.{u}) (F : X.Modules)
    (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (m : Γ(F, U)) :
    genericFractionMap X F η U (LocalizedModule.mk m 1) =
      genericStalkSectionMap X F η U m := by
  simpa only [genericFractionMap] using
    LocalizedModule.lift_mk_one (meromorphicDenominators X U)
      (genericStalkSectionMap X F η U)
      (fun b ↦ generic_factor_denominator_isUnit X η _ U b) m

set_option backward.isDefEq.respectTransparency false in
private theorem genericFractionMap_natural (X : Scheme.{u}) (F : X.Modules)
    (η : {x : X // x ∈ genericPoints X}) {U V : X.Opens} (i : V ⟶ U)
    (z : LocalizedModule (meromorphicDenominators X U) Γ(F, U)) :
    genericFractionMap X F η V (meromorphicRestriction X F i z) =
      ((pushforward (X.fromSpecStalk η.val)).obj
        (tilde (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val)))).presheaf.map
        i.op (genericFractionMap X F η U z) := by
  induction z using LocalizedModule.induction_on with
  | h m b =>
    let N := (pushforward (X.fromSpecStalk η.val)).obj
      (tilde (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val)))
    let c := restrictMeromorphicDenominator X i b
    apply ((Module.End.isUnit_iff _).mp
      (generic_factor_denominator_isUnit X η _ V c)).injective
    change c.val • genericFractionMap X F η V
        (meromorphicRestriction X F i (LocalizedModule.mk m b)) =
      c.val • N.presheaf.map i.op
        (genericFractionMap X F η U (LocalizedModule.mk m b))
    erw [(exists_meromorphicRestriction X F i).choose_spec, ← LinearMap.map_smul,
      show c.val • LocalizedModule.mk (F.presheaf.map i.op m) c =
        LocalizedModule.mk (F.presheaf.map i.op m) 1 by
          rw [LocalizedModule.smul'_mk]
          exact LocalizedModule.mk_cancel c _,
      genericFractionMap_mk_one]
    change _ = X.presheaf.map i.op b.val • N.presheaf.map i.op _
    rw [← Scheme.Modules.map_smul, ← LinearMap.map_smul,
      show b.val • LocalizedModule.mk m b = LocalizedModule.mk m 1 by
        rw [LocalizedModule.smul'_mk]
        exact LocalizedModule.mk_cancel b _, genericFractionMap_mk_one]
    exact genericStalkSectionMap_natural X F η i m

private noncomputable def genericFractionPresheafMap (X : Scheme.{u}) (F : X.Modules)
    (η : {x : X // x ∈ genericPoints X}) :
    meromorphicPresheaf X F ⟶
      ((pushforward (X.fromSpecStalk η.val)).obj
        (tilde (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val)))).val where
  app U := by
    cases U with | op U =>
      exact ModuleCat.ofHom
        (X := (meromorphicPresheaf X F).obj (op U))
        (Y := ((pushforward (X.fromSpecStalk η.val)).obj
          (tilde (ModuleCat.of (X.presheaf.stalk η.val)
            (F.presheaf.stalk η.val)))).val.obj (op U))
        (genericFractionMap X F η U)
  naturality {U V} i := by
    cases U with | op U =>
     cases V with | op V =>
      ext z
      exact genericFractionMap_natural X F η i.unop z

private noncomputable def genericFractionSheafMap (X : Scheme.{u}) (F : X.Modules)
    (η : {x : X // x ∈ genericPoints X}) :
    meromorphicModule X F ⟶
      (pushforward (X.fromSpecStalk η.val)).obj
        (tilde (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val))) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).symm
    (genericFractionPresheafMap X F η)

set_option backward.isDefEq.respectTransparency false in
private theorem genericFractionSheafMap_toMeromorphic (X : Scheme.{u}) (F : X.Modules)
    (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U)
    (m : Γ(F, U)) :
    (toMeromorphicModule X F ≫ genericFractionSheafMap X F η).val.app (op U) m =
      tilde.toOpen (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val))
        (X.fromSpecStalk η.val ⁻¹ᵁ U) (F.presheaf.germ U η.val hη m) := by
  let e := PresheafOfModules.sheafificationHomEquiv
    (𝟙 X.ringCatSheaf.obj) (P := meromorphicPresheaf X F)
    (F := (pushforward (X.fromSpecStalk η.val)).obj
      (tilde (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val))))
  have h := e.apply_symm_apply (genericFractionPresheafMap X F η)
  have hu := congrArg (fun f ↦ (f.app (op U)).hom (LocalizedModule.mk m 1)) h
  change (toMeromorphicModule X F ≫ genericFractionSheafMap X F η).val.app (op U) m = _
  rw [← genericStalkSectionMap_apply X F η U hη]
  rw [← genericFractionMap_mk_one]
  exact hu

private noncomputable def genericProductMap (X : Scheme.{u}) (F : X.Modules) :
    meromorphicModule X F ⟶
      ∏ᶜ (fun η : {x : X // x ∈ genericPoints X} ↦
        (pushforward (X.fromSpecStalk η.val)).obj
          (tilde (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val)))) :=
  Pi.lift (genericFractionSheafMap X F)

private noncomputable def genericProductPresheafMap (X : Scheme.{u}) (F : X.Modules) :
    meromorphicPresheaf X F ⟶
      (∏ᶜ (fun η : {x : X // x ∈ genericPoints X} ↦
        (pushforward (X.fromSpecStalk η.val)).obj
          (tilde (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val))))).val :=
  PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj) (genericProductMap X F)

set_option backward.isDefEq.respectTransparency false in
private theorem genericProductPresheafMap_mk_one (X : Scheme.{u}) (F : X.Modules)
    (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U)
    (m : Γ(F, U)) :
    ((genericProductPresheafMap X F).app (op U) ≫
      (Pi.π (fun ξ : {x : X // x ∈ genericPoints X} ↦
        (pushforward (X.fromSpecStalk ξ.val)).obj
          (tilde (ModuleCat.of (X.presheaf.stalk ξ.val) (F.presheaf.stalk ξ.val))))
        η).val.app (op U)).hom (LocalizedModule.mk m 1) =
      tilde.toOpen (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val))
        (X.fromSpecStalk η.val ⁻¹ᵁ U) (F.presheaf.germ U η.val hη m) := by
  change ((toMeromorphicModule X F ≫ genericProductMap X F ≫
    Pi.π _ η).val.app (op U)) m = _
  rw [genericProductMap, Pi.lift_π]
  exact genericFractionSheafMap_toMeromorphic X F η U hη m

private theorem genericProductPresheafMap_affine_isIso (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent]
    (hweak : ∀ x : X, IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
      Ideal.WeakAss (X.presheaf.stalk x) → x ∈ genericPoints X)
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite)
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso ((genericProductPresheafMap X F).app (op U)) :=
  meromorphic_affine_generic_sections_isIso X F hweak U hU (hfinite U hU.isCompact)
    _ (fun η hη m ↦ genericProductPresheafMap_mk_one X F η U hη m)

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_of_affine_bijective (X : Scheme.{u})
    (P : _root_.PresheafOfModules X.ringCatSheaf.obj) (G : X.Modules)
    (f : (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P ⟶ G)
    (hf : ∀ (U : X.Opens), IsAffineOpen U →
      IsIso (((PresheafOfModules.sheafificationHomEquiv
        (𝟙 X.ringCatSheaf.obj)) f).app (op U))) : IsIso f := by
  let J := _root_.Opens.grothendieckTopology X
  let φ := (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
    (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj) f)
  have hb (U : X.Opens) (hU : IsAffineOpen U) : Function.Bijective (φ.app (op U)) := by
    let := hf U hU
    exact (ConcreteCategory.isIso_iff_bijective _).mp
      (Functor.map_isIso (forget₂ (ModuleCat Γ(X, U)) AddCommGrpCat) _)
  have hi : CategoryTheory.Presheaf.IsLocallyInjective J φ := by
    constructor
    intro U a b hab x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx U.unop.2
    refine ⟨V, homOfLE hVU, ?_, hxV⟩
    apply (hb V hV).injective
    rw [φ.naturality_apply, φ.naturality_apply, hab]
  have hs : CategoryTheory.Presheaf.IsLocallySurjective J φ := by
    apply (TopCat.Presheaf.isLocallySurjective_iff φ).mpr
    intro U a x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    obtain ⟨b, hb⟩ := (hb V hV).surjective (G.presheaf.map (homOfLE hVU).op a)
    exact ⟨V, hVU, ⟨b, hb⟩, hxV⟩
  let ψ := (SheafOfModules.toSheaf X.ringCatSheaf).map f
  have he : φ = CategoryTheory.toSheafify J P.presheaf ≫ ψ.hom := rfl
  have hi' : CategoryTheory.Sheaf.IsLocallyInjective ψ := by
    rw [CategoryTheory.Sheaf.IsLocallyInjective]
    apply (CategoryTheory.Presheaf.comp_isLocallyInjective_iff J
      (CategoryTheory.toSheafify J P.presheaf) ψ.hom).mp
    rwa [← he]
  have hs' : CategoryTheory.Sheaf.IsLocallySurjective ψ := by
    rw [CategoryTheory.Sheaf.IsLocallySurjective]
    apply (CategoryTheory.Presheaf.comp_isLocallySurjective_iff J
      (CategoryTheory.toSheafify J P.presheaf) ψ.hom).mp
    rwa [← he]
  have : IsIso ψ := (CategoryTheory.Sheaf.isLocallyBijective_iff_isIso ψ).mp ⟨hi', hs'⟩
  exact isIso_of_reflects_iso f (SheafOfModules.toSheaf X.ringCatSheaf)

private theorem genericProductMap_isIso (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent]
    (hweak : ∀ x : X, IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
      Ideal.WeakAss (X.presheaf.stalk x) → x ∈ genericPoints X)
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite) : IsIso (genericProductMap X F) :=
  isIso_of_affine_bijective X _ _ _
    (fun U hU ↦ genericProductPresheafMap_affine_isIso X F hweak hfinite U hU)

private noncomputable def unitStalkAddIso (X : Scheme.{u}) (x : X) :
    AddCommGrpCat.of (X.presheaf.stalk x) ≅ (unit X).presheaf.stalk x :=
  preservesColimitIso (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ X.presheaf)

private theorem unitStalkAddIso_germ (X : Scheme.{u}) (x : X)
    (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    (unitStalkAddIso X x).hom (X.presheaf.germ U x hx a) =
      (unit X).presheaf.germ U x hx a := by
  exact CategoryTheory.congr_fun
    (ι_preservesColimitIso_hom (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
      ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ X.presheaf) (op ⟨U, hx⟩)) a

set_option backward.isDefEq.respectTransparency false in
private noncomputable def unitStalkEquiv (X : Scheme.{u}) (x : X) :
    X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] (unit X).presheaf.stalk x := by
  let e := (unitStalkAddIso X x).addCommGroupIsoToAddEquiv
  refine { e with map_smul' := ?_ }
  intro a b
  obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨V, hxV, b, rfl⟩ := X.presheaf.exists_germ_eq b
  let W := U ⊓ V
  have hx : x ∈ W := ⟨hxU, hxV⟩
  rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left : W ⟶ U) x hx a,
    ← X.presheaf.germ_res_apply (homOfLE inf_le_right : W ⟶ V) x hx b]
  change (unitStalkAddIso X x).hom (_ * _) =
    _ • (unitStalkAddIso X x).hom _
  rw [← map_mul, unitStalkAddIso_germ, unitStalkAddIso_germ]
  exact germ_smul (unit X) x hx _ _

private noncomputable def genericUnitFactorIso (X : Scheme.{u})
    (η : {x : X // x ∈ genericPoints X}) :
    (pushforward (X.fromSpecStalk η.val)).obj
        (tilde (ModuleCat.of (X.presheaf.stalk η.val) ((unit X).presheaf.stalk η.val))) ≅
      (pushforward (X.fromSpecStalk η.val)).obj (unit (Spec (X.presheaf.stalk η.val))) :=
  (pushforward (X.fromSpecStalk η.val)).mapIso
    ((tilde.functor (X.presheaf.stalk η.val)).mapIso
      (unitStalkEquiv X η.val).symm.toModuleIso ≪≫ tildeSelf)

set_option backward.isDefEq.respectTransparency false in
private theorem genericUnitFactorIso_formula (X : Scheme.{u})
    (η : {x : X // x ∈ genericPoints X}) :
    toMeromorphicModule X (unit X) ≫ genericFractionSheafMap X (unit X) η ≫
        (genericUnitFactorIso X η).hom =
      SheafOfModules.unitToPushforwardObjUnit
        (X.fromSpecStalk η.val).toRingCatSheafHom := by
  ext U m
  classical
  by_cases hη : η.val ∈ U
  · have hg := genericFractionSheafMap_toMeromorphic X (unit X) η U hη m
    change ((genericUnitFactorIso X η).hom.val.app (op U))
      (((toMeromorphicModule X (unit X) ≫
        genericFractionSheafMap X (unit X) η).val.app (op U)) m) = _
    rw [hg]
    have ht := CategoryTheory.congr_fun
      (tilde.toOpen_map_app ((unitStalkEquiv X η.val).symm.toModuleIso.hom)
        (X.fromSpecStalk η.val ⁻¹ᵁ U))
      ((unit X).presheaf.germ U η.val hη m)
    change (modulesSpecToSheaf.map
      (tilde.map (unitStalkEquiv X η.val).symm.toModuleIso.hom)).hom.app _
        (tilde.toOpen _ _ ((unit X).presheaf.germ U η.val hη m)) = _
    rw [show (modulesSpecToSheaf.map
        (tilde.map (unitStalkEquiv X η.val).symm.toModuleIso.hom)).hom.app _
          (tilde.toOpen _ _ ((unit X).presheaf.germ U η.val hη m)) =
        tilde.toOpen (ModuleCat.of (X.presheaf.stalk η.val) (X.presheaf.stalk η.val))
          (X.fromSpecStalk η.val ⁻¹ᵁ U)
          ((unitStalkEquiv X η.val).symm
            ((unit X).presheaf.germ U η.val hη m)) from ht]
    have he : (unitStalkEquiv X η.val).symm
        ((unit X).presheaf.germ U η.val hη m) =
        X.presheaf.germ U η.val hη m := by
      apply (unitStalkEquiv X η.val).injective
      rw [LinearEquiv.apply_symm_apply]
      exact (unitStalkAddIso_germ X η.val U hη m).symm
    rw [he]
    change _ = (X.fromSpecStalk η.val).app U m
    rw [X.fromSpecStalk_app hη]
    rfl
  · let := generic_factor_sections_subsingleton X η
      (unit (Spec (X.presheaf.stalk η.val))) U hη
    exact Subsingleton.elim _ _

/-- The generic-point product descriptions of the meromorphic sheaf and of the meromorphic
module of a quasi-coherent module. The product isomorphisms are the canonical ones: composed
with `toMeromorphicModule` and the projection at a generic point, the first is the canonical
map O_X → j_{η,*} O_{X,η}, the second sends a section to the image of its germ at η.
The index subtype consists of all generic points of irreducible components, without a
global finiteness assumption. The local-ring module in
each factor is regarded as its associated sheaf on the spectrum of that local ring.
Source: Stacks Project, Divisors, Lemma 31.24.6 (Tag 0EMF)
(blueprint: lem-sc-meromorphic-weakass-generic-product).

Proof:
1. On an affine open Spec A there are finitely many minimal primes q_i by `hfinite`.
   Weak association of a prime is equivalent to weak association at its point (Tag 0566).
   By `hweak` all weakly associated primes are minimal. Apply
   `lem-sc-affine-weakass-nonzerodivisors` and
   `lem-sc-affine-totalquotient-minimal-product` to obtain Q(A) = product_i A_{q_i}.
2. A generic point in this affine open contributes A_{q_i} to its pushforward, and a
   generic point outside contributes zero. The fraction maps in step 1 agree with
   restriction, so these affine-basis identifications glue to the first isomorphism.
3. For a quasi-coherent F with affine module M, tensor the finite decomposition with M:
   Q(A) tensor_A M = product_i (A_{q_i} tensor_A M) = product_i M_{q_i}.
   These localizations are the stalks F_eta. The fraction and restriction maps are
   compatible, giving both isomorphisms in the second and third conjuncts. -/
theorem meromorphicModule_generic_product (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent]
    (hweak : ∀ x : X, IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
      Ideal.WeakAss (X.presheaf.stalk x) → x ∈ genericPoints X)
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite) :
    (∃ e : meromorphicModule X (unit X) ≅
        ∏ᶜ (fun η : {x : X // x ∈ genericPoints X} ↦
          (pushforward (X.fromSpecStalk η.val)).obj (unit (Spec (X.presheaf.stalk η.val)))),
      ∀ η : {x : X // x ∈ genericPoints X},
        toMeromorphicModule X (unit X) ≫ e.hom ≫ Pi.π _ η =
          SheafOfModules.unitToPushforwardObjUnit (X.fromSpecStalk η.val).toRingCatSheafHom) ∧
    Nonempty ((meromorphicModule X (unit X) ⊗ F) ≅ meromorphicModule X F) ∧
    (∃ e : meromorphicModule X F ≅
        ∏ᶜ (fun η : {x : X // x ∈ genericPoints X} ↦
          (pushforward (X.fromSpecStalk η.val)).obj
            (tilde (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val)))),
      ∀ (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U) (m : Γ(F, U)),
        (toMeromorphicModule X F ≫ e.hom ≫ Pi.π _ η).val.app (op U) m =
          tilde.toOpen (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val))
            (X.fromSpecStalk η.val ⁻¹ᵁ U) (F.presheaf.germ U η.val hη m)) := by
  have : (unit X).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have hunit := genericProductMap_isIso X (unit X) hweak hfinite
  have hF := genericProductMap_isIso X F hweak hfinite
  let eunit := asIso (genericProductMap X (unit X)) ≪≫
    Pi.mapIso (genericUnitFactorIso X)
  refine ⟨⟨eunit, ?_⟩, ⟨meromorphicTensorIso X F⟩, asIso (genericProductMap X F), ?_⟩
  · intro η
    change toMeromorphicModule X (unit X) ≫
      (genericProductMap X (unit X) ≫ (Pi.mapIso (genericUnitFactorIso X)).hom) ≫
        Pi.π _ η = _
    simp only [Category.assoc, Pi.mapIso_hom_π, genericProductMap, Pi.lift_π_assoc]
    exact genericUnitFactorIso_formula X η
  · intro η U hη m
    simp only [asIso_hom, genericProductMap, Pi.lift_π]
    exact genericFractionSheafMap_toMeromorphic X F η U hη m

end AlgebraicGeometry.Scheme.Modules
