/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusCohomologyComparisonFactors

/-! # Scalar-and-size tensor cocycle

Source: Deligne, Weil II (1.1.1)(d), (1.1.14), coefficient extension and cohomology
(blueprint: lem-weil-frobenius-cohomology-coefficient-cocycle).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w x u'

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

open scoped TensorProduct ChangeOfRings

namespace WeilConjectures

section TensorCalculations
set_option allowUnsafeReducibility true in
attribute [local reducible] ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'
  ModuleCat.extendScalars ModuleCat.ExtendScalars.obj' ModuleCat.uliftFunctor
  frobeniusCoefficientLiftHom
  ULift.semiring ULift.commRing ULift.ring

private theorem extendScalarsComp_tmul
    {F G H : Type u} [Field F] [Field G] [Field H]
    (φ : F →+* G) (ψ : G →+* H) (M : ModuleCat.{u} F) (c : H) (m : M) :
    (ModuleCat.extendScalarsComp φ ψ).hom.app M (c ⊗ₜ[F, ψ.comp φ] m) =
      c ⊗ₜ[G, ψ] ((1 : G) ⊗ₜ[F, φ] m) := by
  have h := ModuleCat.extendScalarsComp_hom_app_one_tmul φ ψ M m
  have hc := congrArg (fun x ↦ c • x) h
  erw [← map_smul] at hc
  change (ModuleCat.extendScalarsComp φ ψ).hom.app M ((c * 1) ⊗ₜ[F, ψ.comp φ] m) =
    (c * 1) ⊗ₜ[G, ψ] ((1 : G) ⊗ₜ[F, φ] m) at hc
  simpa only [mul_one] using hc

set_option allowUnsafeReducibility true in
attribute [local irreducible] frobeniusCoefficientModules

private theorem moduleTower_coherence
    {F G H : Type u} [Field F] [Field G] [Field H] {Ω : Type v} [Field Ω]
    (φ : F →+* G) (ψ : G →+* H) (χ : H →+* Ω) (M : ModuleCat.{u} F) :
    (frobeniusCoefficientModules χ).map ((ModuleCat.extendScalarsComp φ ψ).inv.app M) ≫
        (frobeniusCoefficientModulesTower_existsUnique (ψ.comp φ) χ).exists.choose.hom.app M =
      (frobeniusCoefficientModulesTower_existsUnique ψ χ).exists.choose.hom.app
          ((ModuleCat.extendScalars φ).obj M) ≫
        (frobeniusCoefficientModulesTower_existsUnique φ (χ.comp ψ)).exists.choose.hom.app M := by
  with_unfolding_all
    let : Module (ULift.{v, u} H) (ULift.{u, v} Ω) :=
      Module.compHom _ (frobeniusCoefficientLiftHom χ)
    let : Module (ULift.{v, u} H)
        (ULift.{v, u} ((ModuleCat.extendScalars (ψ.comp φ)).obj M)) :=
      Module.compHom _ (ULift.ringEquiv : ULift.{v, u} H ≃+* H).toRingHom
    apply (cancel_epi
      ((frobeniusCoefficientModules χ).map ((ModuleCat.extendScalarsComp φ ψ).hom.app M))).1
    rw (transparency := .all) [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
      (frobeniusCoefficientModules χ).map_id, Category.id_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    let α :=
      ((frobeniusCoefficientModulesTower_existsUnique (ψ.comp φ) χ).exists.choose.hom.app M).hom
    let β := (((frobeniusCoefficientModules χ).map ((ModuleCat.extendScalarsComp φ ψ).hom.app M) ≫
      (frobeniusCoefficientModulesTower_existsUnique ψ χ).exists.choose.hom.app
        ((ModuleCat.extendScalars φ).obj M) ≫
      (frobeniusCoefficientModulesTower_existsUnique φ (χ.comp ψ)).exists.choose.hom.app M)).hom
    intro x
    change α x = β x
    induction x using TensorProduct.induction_on with
    | zero => exact α.map_zero.trans β.map_zero.symm
    | add x y hx hy => rw (transparency := .all) [α.map_add, β.map_add, hx, hy]
    | tmul a x =>
      obtain ⟨x⟩ := x
      induction x using TensorProduct.induction_on with
      | zero =>
        rw (transparency := .all) [show (ULift.up (0 : (ModuleCat.extendScalars (ψ.comp φ)).obj M) :
          ULift.{v, u} _) = 0 from rfl, TensorProduct.tmul_zero]
        exact α.map_zero.trans β.map_zero.symm
      | add x y hx hy =>
        rw (transparency := .all) [show (ULift.up (x + y) :
          ULift.{v, u} ((ModuleCat.extendScalars (ψ.comp φ)).obj M)) =
            ULift.up x + ULift.up y from rfl,
          TensorProduct.tmul_add]
        rw (transparency := .all) [α.map_add, β.map_add, hx, hy]
      | tmul c m =>
        change _ =
          (frobeniusCoefficientModulesTower_existsUnique φ (χ.comp ψ)).exists.choose.hom.app M
            ((frobeniusCoefficientModulesTower_existsUnique ψ χ).exists.choose.hom.app
              ((ModuleCat.extendScalars φ).obj M)
              (a ⊗ₜ[ULift.{v, u} H, frobeniusCoefficientLiftHom χ]
                ULift.up ((ModuleCat.extendScalarsComp φ ψ).hom.app M
                  (c ⊗ₜ[F, ψ.comp φ] m))))
        erw [extendScalarsComp_tmul φ ψ M c m]
        have h₁ := (frobeniusCoefficientModulesTower_existsUnique (ψ.comp φ) χ).exists.choose_spec
          M a c m
        have h₂ := (frobeniusCoefficientModulesTower_existsUnique ψ χ).exists.choose_spec
          ((ModuleCat.extendScalars φ).obj M) a c ((1 : G) ⊗ₜ[F, φ] m)
        have h₃ := (frobeniusCoefficientModulesTower_existsUnique φ (χ.comp ψ)).exists.choose_spec
          M (a * ULift.up (χ c)) (1 : G) m
        rw (transparency := .all) [h₁, h₂, h₃]
        simp only [map_one]
        rw (transparency := .all) [show (ULift.up (1 : Ω) : ULift.{u, v} Ω) = 1 from rfl, mul_one]

end TensorCalculations

attribute [local irreducible] HasDerivedCategory.standard
set_option allowUnsafeReducibility true in
attribute [local reducible] frobeniusCohomologyCoefficientExtension
  DerivedCategory.fieldDerivedScalarExtension frobeniusCoefficientModules
  frobeniusCoefficientLiftHom

private instance (priority := 2000) smallModuleDerived (F : Type u) [Field F] :
    HasDerivedCategory.{u} (ModuleCat.{u} F) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

private instance largeModuleDerived (Ω : Type v) [Field Ω] :
    HasDerivedCategory.{(max u v) + 1} (ModuleCat.{max u v} Ω) :=
  HasDerivedCategory.standard _

private instance coefficientModules_additive
    {F : Type u} [Field F] {Ω : Type v} [Field Ω] (χ : F →+* Ω) :
    (frobeniusCoefficientModules χ).Additive := by
  dsimp [frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
  infer_instance

private instance coefficientModules_limits
    {F : Type u} [Field F] {Ω : Type v} [Field Ω] (χ : F →+* Ω) :
    CategoryTheory.Limits.PreservesFiniteLimits (frobeniusCoefficientModules χ) := by
  dsimp [frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
  infer_instance

private instance coefficientModules_colimits
    {F : Type u} [Field F] {Ω : Type v} [Field Ω] (χ : F →+* Ω) :
    CategoryTheory.Limits.PreservesFiniteColimits (frobeniusCoefficientModules χ) := by
  dsimp [frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
  infer_instance

private theorem coefficientTower_fac
    {F G : Type u} [Field F] [Field G] {Ω : Type v} [Field Ω]
    (φ : F →+* G) (χ : G →+* Ω) (K : CochainComplex (ModuleCat.{u} F) ℤ) :
    (frobeniusCoefficientTower φ χ).hom.app (DerivedCategory.Q.obj K) ≫
        (frobeniusCoefficientModules (χ.comp φ)).mapDerivedCategoryFactors.hom.app K =
      (frobeniusCohomologyCoefficientExtension χ).map
          ((ModuleCat.extendScalars φ).mapDerivedCategoryFactors.hom.app K) ≫
        (frobeniusCoefficientModules χ).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((CategoryTheory.Functor.mapHomologicalComplexCompIso
            (frobeniusCoefficientModulesTower_existsUnique φ χ).exists.choose (.up ℤ)).hom.app K)
      := by
  let e := (frobeniusCoefficientModulesTower_existsUnique φ χ).exists.choose
  let T := ModuleCat.extendScalars φ
  let A := frobeniusCoefficientModules χ
  let B := frobeniusCoefficientModules (χ.comp φ)
  have hid : (CategoryTheory.Functor.mapHomologicalComplexCompIso
      (Iso.refl (T ⋙ A)) (.up ℤ)).hom.app K =
      𝟙 _ := by ext n; rfl
  have hc := CategoryTheory.Functor.mapDerivedCategoryCompIso_fac T A K
  simp only [hid] at hc
  simp only [CategoryTheory.Functor.comp_obj] at hc
  erw [CategoryTheory.Functor.map_id] at hc
  erw [Category.comp_id] at hc
  apply (cancel_epi ((CategoryTheory.Functor.mapDerivedCategoryCompIso T A).hom.app
    (DerivedCategory.Q.obj K))).1
  change (CategoryTheory.Functor.mapDerivedCategoryCompIso T A).hom.app (DerivedCategory.Q.obj K) ≫
      ((CategoryTheory.Functor.mapDerivedCategoryCompIso T A).inv.app (DerivedCategory.Q.obj K) ≫
        (CategoryTheory.Functor.mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj K)) ≫
      B.mapDerivedCategoryFactors.hom.app K = _
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [CategoryTheory.Functor.mapDerivedCategoryNatIso_fac]
  change _ = (CategoryTheory.Functor.mapDerivedCategoryCompIso T A).hom.app
      (DerivedCategory.Q.obj K) ≫
    A.mapDerivedCategory.map (T.mapDerivedCategoryFactors.hom.app K) ≫
      A.mapDerivedCategoryFactors.hom.app ((T.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K)
  erw [← hc]
  rw (transparency := .all) [Category.assoc, Category.assoc]
  with_unfolding_all rfl



private theorem fieldTower_fac
    {F G H : Type u} [Field F] [Field G] [Field H]
    (φ : F →+* G) (ψ : G →+* H) (K : CochainComplex (ModuleCat.{u} F) ℤ) :
    (DerivedCategory.fieldScalarTower φ ψ).hom.app (DerivedCategory.Q.obj K) ≫
        (ModuleCat.extendScalars (ψ.comp φ)).mapDerivedCategoryFactors.hom.app K =
      (DerivedCategory.fieldDerivedScalarExtension ψ).map
          ((ModuleCat.extendScalars φ).mapDerivedCategoryFactors.hom.app K) ≫
        (ModuleCat.extendScalars ψ).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((CategoryTheory.Functor.mapHomologicalComplexCompIso
            (ModuleCat.extendScalarsComp φ ψ).symm
            (.up ℤ)).hom.app K) := by
  rw [show (DerivedCategory.fieldScalarTower φ ψ).hom.app (DerivedCategory.Q.obj K) =
      (DerivedCategory.fieldScalarTowerComponent φ ψ K).hom from
    congrArg Iso.hom ((DerivedCategory.existsUnique_fieldScalarTower φ ψ).exists.choose_spec K)]
  simp only [DerivedCategory.fieldScalarTowerComponent, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Category.assoc,
    Iso.inv_hom_id_app]
  simp only [CategoryTheory.Functor.comp_obj, Category.comp_id]

private theorem coefficientTower_assoc
    {F G H : Type u} [Field F] [Field G] [Field H] {Ω : Type v} [Field Ω]
    (φ : F →+* G) (ψ : G →+* H) (χ : H →+* Ω)
    (V : @DerivedCategory (ModuleCat.{u} F) _ _
      (HasDerivedCategory.ofIsGrothendieckAbelian.{u} _)) :
    (frobeniusCohomologyCoefficientExtension χ).map
        ((DerivedCategory.fieldScalarTower φ ψ).hom.app V) ≫
        (frobeniusCoefficientTower (ψ.comp φ) χ).hom.app V =
      (frobeniusCoefficientTower ψ χ).hom.app
          ((DerivedCategory.fieldDerivedScalarExtension φ).obj V) ≫
        (frobeniusCoefficientTower φ (χ.comp ψ)).hom.app V := by
  let f := CategoryTheory.Functor.whiskerRight (DerivedCategory.fieldScalarTower φ ψ).hom
      (frobeniusCohomologyCoefficientExtension χ) ≫
    (frobeniusCoefficientTower (ψ.comp φ) χ).hom
  let g := CategoryTheory.Functor.whiskerLeft (DerivedCategory.fieldDerivedScalarExtension φ)
      (frobeniusCoefficientTower ψ χ).hom ≫
    (frobeniusCoefficientTower φ (χ.comp ψ)).hom
  have he : f = g := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} F) (.up ℤ))
    intro K
    let TK := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K
    let A := frobeniusCoefficientModules χ
    let B := frobeniusCoefficientModules ((χ.comp ψ).comp φ)
    let c := (CategoryTheory.Functor.mapHomologicalComplexCompIso
      (ModuleCat.extendScalarsComp φ ψ).symm
      (.up ℤ)).hom.app K
    have hc : (A.mapHomologicalComplex (.up ℤ)).map c ≫
        (CategoryTheory.Functor.mapHomologicalComplexCompIso
          (frobeniusCoefficientModulesTower_existsUnique (ψ.comp φ) χ).exists.choose
          (.up ℤ)).hom.app K =
      (CategoryTheory.Functor.mapHomologicalComplexCompIso
          (frobeniusCoefficientModulesTower_existsUnique ψ χ).exists.choose
          (.up ℤ)).hom.app TK ≫
        (CategoryTheory.Functor.mapHomologicalComplexCompIso
          (frobeniusCoefficientModulesTower_existsUnique φ (χ.comp ψ)).exists.choose
          (.up ℤ)).hom.app K := by
      apply HomologicalComplex.Hom.ext
      funext i
      exact moduleTower_coherence φ ψ χ (K.X i)
    have hQ := congrArg DerivedCategory.Q.map hc
    simp only [CategoryTheory.Functor.map_comp] at hQ
    have hn := (frobeniusCoefficientTower ψ χ).hom.naturality
      ((ModuleCat.extendScalars φ).mapDerivedCategoryFactors.hom.app K)
    apply (cancel_mono (B.mapDerivedCategoryFactors.hom.app K)).1
    simp only [f, g, NatTrans.comp_app, CategoryTheory.Functor.whiskerLeft_app,
      CategoryTheory.Functor.whiskerRight_app, Category.assoc]
    change (frobeniusCohomologyCoefficientExtension χ).map
        ((DerivedCategory.fieldScalarTower φ ψ).hom.app (DerivedCategory.Q.obj K)) ≫
      (frobeniusCoefficientTower (ψ.comp φ) χ).hom.app (DerivedCategory.Q.obj K) ≫
      B.mapDerivedCategoryFactors.hom.app K =
      (frobeniusCoefficientTower ψ χ).hom.app
          ((DerivedCategory.fieldDerivedScalarExtension φ).obj (DerivedCategory.Q.obj K)) ≫
        (frobeniusCoefficientTower φ (χ.comp ψ)).hom.app (DerivedCategory.Q.obj K) ≫
      B.mapDerivedCategoryFactors.hom.app K
    erw [coefficientTower_fac, coefficientTower_fac]
    rw [← reassoc_of% hn]
    rw [reassoc_of% (coefficientTower_fac ψ χ TK)]
    rw [← CategoryTheory.Functor.map_comp_assoc, fieldTower_fac]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [reassoc_of% A.mapDerivedCategoryFactors_hom_naturality c]
    rw [hQ]
  exact congr_app he V


set_option allowUnsafeReducibility true in
attribute [local irreducible] frobeniusCohomologyCoefficientExtension
  DerivedCategory.fieldDerivedScalarExtension frobeniusCoefficientModules
  frobeniusCoefficientLiftHom frobeniusCoefficientTower DerivedCategory.fieldScalarTower
  CohomologyRealization.scalarAssociator CohomologyRealization.coefficientRingComparison

namespace CohomologyRealization

/-- The scalar-and-size comparison obeys the balanced tensor tower equation.
Source: Deligne, Weil II (1.1.1)(d), (1.1.14), coefficient enlargement;
Step 2 of lem-weil-frobenius-cohomology-realization-transport
(blueprint: lem-weil-frobenius-cohomology-coefficient-cocycle).

Proof: first compare the ordinary module functors. Precompose both routes with
its invertible field tensor associator, so two tensor inductions suffice. On a
pure tensor a tensor b tensor m, with a in Ω and b in N, the direct route gives
a times the image of b, tensored with m. The other route splits off the scalar
one in L and gives the same result. The defining
normalization of frobeniusCoefficientModulesTower_existsUnique identifies these
maps with the balanced tensor comparisons. Two tensor inductions prove equality
on all module elements. Apply the induced functors on complexes and localization
to obtain the derived identity; the factorization isomorphisms cancel by
naturality. The equalities of the coefficient inclusions and stage embeddings
identify the direct composite with the displayed direct comparison. These
arguments use the same multiplication maps for repeated fields and zero modules.
No geometric operation or cohomology functor is involved. -/
theorem coefficientComparison_cocycle
    {F G H : Type u} [Field F] [Field G] [Field H] {Ω : Type v} [Field Ω]
    (φ : F →+* G) (ψ : G →+* H) (θ : F →+* H)
    (ξ : F →+* Ω) (η : G →+* Ω) (χ : H →+* Ω)
    (hcomp : ψ.comp φ = θ) (hφ : η.comp φ = ξ) (hψ : χ.comp ψ = η)
    (hθ : χ.comp θ = ξ)
    (V : @DerivedCategory (ModuleCat.{u} F) _ _
      (HasDerivedCategory.ofIsGrothendieckAbelian.{u} _)) :
    letI : HasDerivedCategory.{u} (ModuleCat.{u} F) :=
      HasDerivedCategory.ofIsGrothendieckAbelian _
    letI : HasDerivedCategory.{u} (ModuleCat.{u} G) :=
      HasDerivedCategory.ofIsGrothendieckAbelian _
    letI : HasDerivedCategory.{u} (ModuleCat.{u} H) :=
      HasDerivedCategory.ofIsGrothendieckAbelian _
    letI : HasDerivedCategory.{(max u v) + 1} (ModuleCat.{max u v} Ω) :=
      HasDerivedCategory.standard _
    (frobeniusCohomologyCoefficientExtension χ).map
        ((scalarAssociator φ ψ θ hcomp).hom.app V) ≫
        (coefficientRingComparison θ χ ξ hθ).hom.app V =
      (coefficientRingComparison ψ χ η hψ).hom.app
          ((DerivedCategory.fieldDerivedScalarExtension φ).obj V) ≫
        (coefficientRingComparison φ η ξ hφ).hom.app V := by
  subst θ
  subst η
  subst ξ
  simpa only [scalarAssociator, coefficientRingComparison, Iso.trans_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_refl, eqToHom_app, Category.comp_id,
    CategoryTheory.Functor.map_comp] using coefficientTower_assoc φ ψ χ V

attribute [-instance] smallModuleDerived largeModuleDerived
  coefficientModules_additive coefficientModules_limits coefficientModules_colimits

/-- The tensor cocycle as an equality of the specified natural isomorphisms.
Source: Deligne, Weil II (1.1.1)(d), iterated coefficient extension
(blueprint: lem-weil-frobenius-cohomology-coefficient-cocycle).

Proof: natural isomorphisms are determined by their hom components. Their
component equation is coefficientComparison_cocycle, since the associator has
identity components. -/
theorem coefficientComparison_isoCocycle
    {F G H : Type u} [Field F] [Field G] [Field H] {Ω : Type v} [Field Ω]
    (φ : F →+* G) (ψ : G →+* H) (θ : F →+* H)
    (ξ : F →+* Ω) (η : G →+* Ω) (χ : H →+* Ω)
    (hcomp : ψ.comp φ = θ) (hφ : η.comp φ = ξ) (hψ : χ.comp ψ = η)
    (hθ : χ.comp θ = ξ) :
    Functor.isoWhiskerRight (scalarAssociator φ ψ θ hcomp)
        (frobeniusCohomologyCoefficientExtension χ) ≪≫ coefficientRingComparison θ χ ξ hθ =
      Functor.associator (DerivedCategory.fieldDerivedScalarExtension φ)
          (DerivedCategory.fieldDerivedScalarExtension ψ)
          (frobeniusCohomologyCoefficientExtension χ) ≪≫
        Functor.isoWhiskerLeft (DerivedCategory.fieldDerivedScalarExtension φ)
          (coefficientRingComparison ψ χ η hψ) ≪≫ coefficientRingComparison φ η ξ hφ := by
  apply Iso.ext
  apply NatTrans.ext
  funext V
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] using
    coefficientComparison_cocycle φ ψ θ ξ η χ hcomp hφ hψ hθ V

/-- The specified coefficient record, bundled with the proved balanced tensor law.
Source: Deligne, Weil II (1.1.1)(d), iterated coefficient extension
(blueprint: def-weil-frobenius-cohomology-canonical-factors). -/
def coefficientDataOfFields {I : Type u'} [Preorder I]
    (K : I → Type u) [fieldFamily : ∀ i, Field (K i)]
    (Ω : Type v) [Field Ω]
    (ι : ∀ (i j : I), i ≤ j → K i →+* K j) (e : ∀ i, K i →+* Ω)
    (hc : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
      (ι j k h').comp (ι i j h) = ι i k (h.trans h'))
    (he : ∀ (i j : I) (h : i ≤ j), (e j).comp (ι i j h) = e i) :
    {d : CoefficientData
      (B := fun i ↦ @DerivedCategory (ModuleCat.{u} (K i)) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian.{u} _))
      (bCategory := fieldDerivedCategoryFamily K)
      (D := @DerivedCategory (ModuleCat.{max u v} Ω) _ _ (HasDerivedCategory.standard _)) //
      factorCoefficientCocycle (bCategory := fieldDerivedCategoryFamily K) d} := by
  letI := fieldDerivedCategoryFamily K
  exact coefficientDataWithCocycle (bCategory := fieldDerivedCategoryFamily K)
    (fun i ↦ frobeniusCohomologyCoefficientExtension (e i))
    (fun i j h ↦ DerivedCategory.fieldDerivedScalarExtension (ι i j h))
    (fun i j k h h' ↦ scalarAssociator (ι i j h) (ι j k h') (ι i k (h.trans h'))
      (hc i j k h h'))
    (fun i j h ↦ coefficientRingComparison (ι i j h) (e j) (e i) (he i j h))
    (fun i j k h h' ↦ coefficientComparison_isoCocycle
      (ι i j h) (ι j k h') (ι i k (h.trans h')) (e i) (e j) (e k)
      (hc i j k h h') (he i j h) (he j k h') (he i k (h.trans h')))

/-- The field-system record has its recorded tensor coherence proof.
Source: Deligne, Weil II (1.1.1)(d), iterated coefficient extension
(blueprint: def-weil-frobenius-cohomology-canonical-factors).

Proof: take the proof field of the explicit coefficient-data constructor. -/
theorem coefficientDataOfFields_cocycle {I : Type u'} [Preorder I]
    (K : I → Type u) [fieldFamily : ∀ i, Field (K i)]
    (Ω : Type v) [Field Ω]
    (ι : ∀ (i j : I), i ≤ j → K i →+* K j) (e : ∀ i, K i →+* Ω)
    (hc : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
      (ι j k h').comp (ι i j h) = ι i k (h.trans h'))
    (he : ∀ (i j : I) (h : i ≤ j), (e j).comp (ι i j h) = e i) :
    factorCoefficientCocycle (bCategory := fieldDerivedCategoryFamily K)
      (coefficientDataOfFields K Ω ι e hc he).val :=
  (coefficientDataOfFields K Ω ι e hc he).property

/-- The coefficient factors, independent of the scheme and its cohomology.
Source: Deligne, Weil II (1.1.1)(d), iterated coefficient extension
(blueprint: def-weil-frobenius-cohomology-canonical-factors). -/
def coefficientParts
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] :
    CoefficientData
      (B := fun E : AlgebraicallyClosedCoefficients.Index l Ω ↦
        @DerivedCategory (ModuleCat.{u} (AlgebraicallyClosedCoefficients.Coefficient l Ω E))
          _ _ (HasDerivedCategory.ofIsGrothendieckAbelian.{u} _))
      (bCategory := coefficientDerivedCategoryFamily.{u, v} l Ω)
      (D := @DerivedCategory (ModuleCat.{max u v} Ω) _ _ (HasDerivedCategory.standard _)) :=
  (coefficientDataOfFields (fieldFamily := fun _ ↦ inferInstance)
    (fun E : AlgebraicallyClosedCoefficients.Index l Ω ↦
      AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) Ω
    (fun E L h ↦
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω E L h).toRingHom)
    (frobeniusCohomologyStageEmbedding.{u, v} l Ω)
    (fun E L N h k ↦ congrArg AlgHom.toRingHom
      ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L N h k))
    (frobeniusCohomologyStageEmbedding_comp l Ω)).val

/-- The canonical coefficient record satisfies the tensor tower equation.
Source: Deligne, Weil II (1.1.1)(d), iterated coefficient extension
(blueprint: def-weil-frobenius-cohomology-canonical-factors).

Proof: specialize the recorded generic coherence proof to the coefficient
inclusions and stage embeddings, using their stated composition laws. -/
theorem coefficientParts_cocycle
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] :
    factorCoefficientCocycle (bCategory := coefficientDerivedCategoryFamily.{u, v} l Ω)
      (coefficientParts l Ω) :=
  coefficientDataOfFields_cocycle (fieldFamily := fun _ ↦ inferInstance)
    (fun E : AlgebraicallyClosedCoefficients.Index l Ω ↦
      AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) Ω
    (fun E L h ↦
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω E L h).toRingHom)
    (frobeniusCohomologyStageEmbedding.{u, v} l Ω)
    (fun E L N h k ↦ congrArg AlgHom.toRingHom
      ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L N h k))
    (frobeniusCohomologyStageEmbedding_comp l Ω)

open AlgebraicallyClosedCoefficients (Index)
open GeneralAlgebraicallyClosedCoefficients (stageSystem)

/-- The canonical factor record, constructed from the prescribed cohomology and tensor maps.
Source: Deligne, Weil II (1.1.1)(d), (1.1.14), iterated coefficient extension
(blueprint: def-weil-frobenius-cohomology-canonical-factors). -/
def realizationParts
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (c₀ : Compactification Y₀.hom) (compact : Bool)
    : FactorData
      (B := fun E : Index l Ω ↦
        @DerivedCategory (ModuleCat.{u} (AlgebraicallyClosedCoefficients.Coefficient l Ω E))
          _ _ (HasDerivedCategory.ofIsGrothendieckAbelian.{u} _))
      (bCategory := coefficientDerivedCategoryFamily.{u, v} l Ω)
      (D := @DerivedCategory (ModuleCat.{max u v} Ω) _ _ (HasDerivedCategory.standard _))
      (stageSystem l Ω (D.geometricFiber Y₀).left) := by
  letI := coefficientDerivedCategoryFamily.{u, v} l Ω
  exact {
    toCoefficientData := coefficientParts l Ω
    H := CohomologyRealization.rationalStage l Ω D hl Y₀ c₀ compact
    q := CohomologyRealization.rationalComparison l Ω D hl Y₀ c₀ compact }

end CohomologyRealization
end WeilConjectures
