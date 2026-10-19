/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

import all Sheaf.Paper.IntegralConstantModelHeartClosure
import all Sheaf.Paper.IndHeartFullFaithfulness
import all Sheaf.Paper.IndHeartCanonicalPresentation
import all Sheaf.Paper.IndHeartKernelsCokernels
import all Sheaf.Paper.IndConstructibleExtensions
import all Sheaf.Paper.CoefficientHeartSmall
import all Sheaf.Paper.ConstructibleExtContinuity
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Sheaf.SixFunctors.IntegralExtHomContinuity
import Sheaf.Paper.IntegralConstructibleSerre
import Mathlib.CategoryTheory.Abelian.Subcategory

/-! # Weak Serre closure for integral adic coefficients

Source: blueprint `sk-prop-ind-heart` and `det-prop-int-compactness-compact` (1)-(2).
The filtered colimits are taken in the ordinary category of internal module sheaves.
(blueprint: new-lem-sfb-integral-ind-heart-weak-serre)
-/

@[expose] public section

set_option autoImplicit false


universe u

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem embedded_integralCoefficientIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    Nonempty (Mon.mk (integralCondensedRing ℓ (ULift.{u} E)) ≅
      Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E)) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let : NormedAlgebra ℚ_[ℓ] E :=
    ⟨fun a x ↦ by
      change ‖algebraMap E (PadicAlgCl ℓ) (a • x)‖ ≤
        ‖a‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
        PadicAlgCl.norm_extends]⟩
  let F := ULift.{u} E
  let : NormedField F :=
    { (inferInstance : Field F), (inferInstance : NormedCommRing F) with
      dist_eq x y := dist_eq_norm_neg_add x.down y.down
      norm_mul x y := norm_mul x.down y.down }
  let : NormedAlgebra ℚ_[ℓ] F := ⟨fun a x ↦ by
    change ‖a • x.down‖ ≤ ‖a‖ * ‖x.down‖
    exact norm_smul_le a x.down⟩
  let : FiniteDimensional ℚ_[ℓ] F :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E)).symm.finiteDimensional
  let A := latticeCoefficientIntegers ℓ F
  let e : WithAbs (Padic.coefficientExtensionAbsoluteValue ℓ F) ≃+* E :=
    (WithAbs.equiv _).trans ULift.ringEquiv
  have he (x : WithAbs (Padic.coefficientExtensionAbsoluteValue ℓ F)) : ‖e x‖ = ‖x‖ := by
    change ‖(WithAbs.equiv _ x).down‖ = spectralNorm ℚ_[ℓ] F (WithAbs.equiv _ x)
    exact NormedAlgebra.norm_eq_spectralNorm ℚ_[ℓ] (L := F) (WithAbs.equiv _ x)
  have hmem (x : WithAbs (Padic.coefficientExtensionAbsoluteValue ℓ F)) :
      x ∈ A ↔ e x ∈ PadicAlgCl.integers ℓ E := by
    have hm := (Padic.extension_integers_dvr ℓ F
      (Padic.coefficientExtensionAbsoluteValue ℓ F)
      (spectralNorm_extends (K := ℚ_[ℓ]) (L := F))).choose_spec.choose_spec.1
    change WithAbs.equiv _ x ∈ Padic.coefficientExtensionIntegers ℓ F ↔ _
    change ∀ y : F, y ∈ Padic.coefficientExtensionIntegers ℓ F ↔
      Padic.coefficientExtensionAbsoluteValue ℓ F y ≤ 1 at hm
    rw [hm, PadicAlgCl.mem_integers_iff]
    change ‖x‖ ≤ 1 ↔ ‖e x‖₊ ≤ 1
    rw [← he, ← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm]
  let ei : A ≃+* PadicAlgCl.integers ℓ E :=
    { toFun := fun x ↦ ⟨e x, (hmem x).mp x.property⟩
      invFun := fun x ↦ ⟨e.symm x,
        (hmem _).mpr (by simpa only [e.apply_symm_apply] using x.property)⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x)
      right_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x)
      map_mul' := fun x y ↦ Subtype.ext (e.map_mul x y)
      map_add' := fun x y ↦ Subtype.ext (e.map_add x y) }
  have hei : Isometry ei := by
    apply AddMonoidHomClass.isometry_of_norm ei
    intro x
    exact he x
  have heis : Isometry ei.symm := by
    intro x y
    simpa only [ei.apply_symm_apply] using (hei (ei.symm x) (ei.symm y)).symm
  let eR : Profinite.continuousMapRingSheafOfUniverse.{u,u} A ≅
      Profinite.padicIntegersCondensedRing.{u} ℓ E :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.toRingHom.compLeftContinuous S.unop hei.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.symm.toRingHom.compLeftContinuous S.unop
              heis.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.apply_symm_apply _ }
  let eAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom eAb.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  have : IsMonHom eAb.inv := Sheaf.isMonHom_sheafCompose_map _ eR.inv
  set_option backward.isDefEq.respectTransparency false in
    refine ⟨{ hom := Mon.ofHom eAb.hom
              inv := Mon.ofHom eAb.inv
              hom_inv_id := ?_
              inv_hom_id := ?_ }⟩
  · apply Mon.Hom.ext
    exact eAb.hom_inv_id
  · apply Mon.Hom.ext
    exact eAb.inv_hom_id

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem integral_constructible_eq
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] :
    IsConstructibleModuleObject (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X) =
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X := by
  obtain ⟨e⟩ := embedded_integralCoefficientIso.{u} ℓ E
  let φ := e.hom.hom
  have : IsMonHom φ := inferInstanceAs (IsMonHom e.hom.hom)
  have : IsIso φ := inferInstanceAs (IsIso e.hom.hom)
  let ψ := coefficientMap φ X
  funext M
  apply propext
  have hp := integralLfpConstantModelComparison ℓ (ULift.{u} E) X ((Mod.comap ψ).obj M)
  constructor
  · intro h
    exact (constantModel_comap_iff φ X M).mp (hp.mp (_root_.constructible_comap ψ h))
  · intro h
    have hh := hp.mpr ((constantModel_comap_iff φ X M).mpr h)
    exact _root_.constructible_of_iso
      (((Mod.comapComp (inv ψ) ψ).symm ≪≫ Mod.comapCongr (by simp) ≪≫
        Mod.comapId _).app M) (_root_.constructible_comap (inv ψ) hh)

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (X : Over (Spec (.of k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

include k in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem integral_sheaf_ext_continuity
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (C : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left))
    (hC : IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X.left C)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (M : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left))
    (c : Cocone M) (hc : IsColimit c) (q : ℤ) :
    IsIso (colimit.desc _
      (((DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
        preadditiveCoyoneda.obj
          (Opposite.op ((DerivedCategory.singleFunctor _ 0).obj C))).mapCocone c))) := by
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E
  let C' := (DerivedCategory.singleFunctor _ 0).obj C
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have hcmp := integral_constructible_eq ℓ E X.left
  have hCs : IsConstructibleModuleObject (condensedRingObj Λ X.left) C := hcmp.symm ▸ hC
  have hC' : constantModelBoundedConstructible Λ X.left C' := by
    refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
    by_cases hn : n = 0
    · subst n
      rw [← hcmp]
      exact AlgebraicGeometry.ProEtale.constructible_of_iso _
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app C).symm hCs
    · rw [← hcmp]
      apply AlgebraicGeometry.ProEtale.constructible_of_isZero
      rcases lt_or_gt_of_ne hn with hn | hn
      · exact DerivedCategory.isZero_of_isGE _ 0 n hn
      · exact DerivedCategory.isZero_of_isLE _ 0 n hn
  let K := M ⋙ CochainComplex.singleFunctor _ 0
  let G := DerivedCategory.Q ⋙ shiftFunctor _ q ⋙ preadditiveCoyoneda.obj (Opposite.op C')
  have hK : ∀ (i : I) (r : ℤ), r < 0 → IsZero ((K.obj i).X r) := by
    intro i r hr
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (M.obj i) r (ne_of_lt hr)
  have hmain : IsIso (colimit.post K G) :=
    integralExtHomContinuous (X := X) C' hC' K 0 hK q
  have : PreservesColimit K G := preservesColimit_of_isIso_post G K
  have : PreservesColimit M (CochainComplex.singleFunctor _ 0) := by
    change PreservesColimit M (HomologicalComplex.single _ (.up ℤ) 0)
    infer_instance
  have hc' := isColimitOfPreserves G
    (isColimitOfPreserves (CochainComplex.singleFunctor _ 0) hc)
  exact ((colimit.isColimit _).nonempty_isColimit_iff_isIso_desc).mp ⟨hc'⟩

include k

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The ambient filtered-colimit closure of integral constructibles is weak Serre.

Source: blueprint `det-prop-int-compactness-compact`, proof steps 1--7,
and `det-lem-int-ext-continuity`.
(blueprint: new-lem-sfb-integral-ind-heart-weak-serre)

Proof: identify locally finitely presented integral modules on each noetherian stratum
with finite constant scalar models using continuous Smith presentations. Constructible
modules are closed under kernels, cokernels and extensions. Present an arrow between two
filtered constructible colimits over the filtered category of finite-stage squares;
finite presentation descends the arrows and their equality relations. Exact filtered
colimits then compute its kernel and cokernel from constructible kernels and cokernels.
For extensions, pull back to each constructible stage of the quotient. Integral Ext^1
continuity descends the extension class to a constructible stage of the subobject.
Push out that finite-stage extension and take filtered colimits over both stages. The
short five lemma identifies the result with the given extension. This uses no uniform
Ext-degree bound and therefore no finiteness assumption on the base field. Rank zero,
torsion modules, empty strata and the zero object are included in the same argument. -/
theorem ellAdic_integral_indConstructible_weakSerre :
    ∀ (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
      [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E],
      let P := ObjectProperty.ind.{u + 1}
        (IsConstructibleModuleObject
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left))
      P.IsClosedUnderKernels ∧ P.IsClosedUnderCokernels ∧ P.IsClosedUnderExtensions := by
  intro E _ _ _ _ _
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E
  let C : ObjectProperty _ := IsConstructibleModuleObject (condensedRingObj Λ X.left)
  let P : ObjectProperty _ := IsConstantModelConstructible Λ X.left
  let Q := ObjectProperty.ind.{u + 1} P
  have hcmp : C = P := integral_constructible_eq ℓ E X.left
  change C.ind.IsClosedUnderKernels ∧ C.ind.IsClosedUnderCokernels ∧
    C.ind.IsClosedUnderExtensions
  rw [hcmp]
  have : P.IsClosedUnderIsomorphisms := by
    rw [← hcmp]
    exact ⟨fun e h ↦ AlgebraicGeometry.ProEtale.constructible_of_iso _ e h⟩
  have : P.ContainsZero := by
    rw [← hcmp]
    exact ⟨0, isZero_zero _,
      AlgebraicGeometry.ProEtale.constructible_of_isZero _ (isZero_zero _)⟩
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let : NormedAlgebra ℚ_[ℓ] E :=
    ⟨fun a x ↦ by
      change ‖algebraMap E (PadicAlgCl ℓ) (a • x)‖ ≤
        ‖a‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
        PadicAlgCl.norm_extends]⟩
  obtain ⟨hk, hq, he⟩ := integralConstructible_serre ℓ E X.left
  have hPk : P.IsClosedUnderKernels := by rw [← hcmp]; exact hk
  have hPq : P.IsClosedUnderCokernels := by rw [← hcmp]; exact hq
  have : P.IsClosedUnderExtensions := by rw [← hcmp]; exact he
  have : P.IsClosedUnderBinaryProducts := by
    apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
    rintro _ ⟨F, hF⟩
    let e : F ≅ pair (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩) :=
      Discrete.natIso (fun j ↦ by cases j with | mk j => cases j <;> exact Iso.refl _)
    exact P.prop_of_iso ((biprod.isoProd _ _).trans (HasLimit.isoOfNatIso e).symm)
      (P.prop_biprod (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩))
  have : P.IsClosedUnderFiniteProducts := ObjectProperty.IsClosedUnderFiniteProducts.mk'
  have : HasBinaryBiproducts P.FullSubcategory :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have : Abelian P.FullSubcategory := inferInstance
  have {M N : P.FullSubcategory} (f : M ⟶ N) :
      PreservesColimit (parallelPair f 0) P.ι := P.preservesCokernels_ι f
  have : PreservesFiniteColimits P.ι :=
    Functor.preservesFiniteColimits_of_preservesCokernels P.ι
  have hsmall : EssentiallySmall.{u + 1} P.FullSubcategory := by
    have hs := stratifiedModelsSmall Λ X.left
    have : ObjectProperty.EssentiallySmall.{u + 1}
        (IsConstantModelConstructible Λ X.left) := by
      rw [show IsConstantModelConstructible Λ X.left = IsFiniteConstantStratified Λ X.left by
        funext M
        exact if_pos ⟨inferInstance, inferInstance⟩]
      exact hs
    infer_instance
  have hfp : P ≤ ObjectProperty.isFinitelyPresentable.{u + 1} _ := by
    intro C hC
    let S := DerivedCategory.singleFunctor
      (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj Λ X.left)) 0
    apply finitelyPresentable_of_continuity (S ⋙ shiftFunctor _ (0 : ℤ))
      C (S.obj C) ((shiftFunctorZero _ ℤ).app (S.obj C))
    intro J _ _ M
    exact integral_sheaf_ext_continuity ℓ X E C hC M
      (colimit.cocone M) (colimit.isColimit M) 0
  have hpres : IndHeartCanonicalPresentationAssertions Λ X.left :=
    canonicalPresentation_of_finitePresentation Λ X.left hsmall
      (fun A ↦ hfp _ A.property)
  have hKC := assertions_of_closure Λ X.left hsmall ⟨inferInstance⟩
    inferInstance hPk hPq hpres
  have : Q.IsClosedUnderKernels := by
    constructor
    rintro _ ⟨f, c, hc, hA, hB⟩
    obtain ⟨_, _, _, _, _, _, _, h, _⟩ := hKC _ _ f hA hB
    exact Q.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hc) h
  have : Q.IsClosedUnderCokernels := by
    constructor
    rintro _ ⟨f, c, hc, hA, hB⟩
    obtain ⟨_, _, _, _, _, _, _, _, h⟩ := hKC _ _ f hA hB
    exact Q.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hc) h
  have : Q.IsClosedUnderExtensions := by
    constructor
    intro S hS hA hB
    apply ind_extension_of_finitelyPresentable P hfp _ S hS hA hB
    intro C hC J _ _ N pres hp ξ
    apply ext_stage_of_comparison C pres _ ξ
    exact integral_sheaf_ext_continuity ℓ X E C hC pres.diag
      (Cocone.mk N pres.ι) pres.isColimit 1
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry.ProEtale.CondensedRing
