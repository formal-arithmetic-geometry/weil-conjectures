/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarMateIdentifications
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionFormulaArrows
import all WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.IndependentExtensionTensor.ExtensionTensorComparisonIndependent
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators

/-! # Ordinary scalar balancing and its unbounded chain comparison

Source: Stacks Project, Modules on Sites, Tag 03EL, lemma-tensor-product-pullback;
Homology, Tag 012Z (blueprint: lem-sp-section-scalar-balancing-chain).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings

namespace AlgebraicGeometry.ProEtale

/-- Concrete sheafified extension of scalars, with no legacy model choice.
Source: Stacks 03CX (blueprint: lem-sp-proetale-concrete-scalar-extension). -/
def scalarBalancingExtension {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (Y : Scheme.{u}) :
    proEtaleRingModules Y (proEtaleConstantRing Y A) ⥤
      proEtaleRingModules Y (proEtaleConstantRing Y B) := by
  let a := proEtaleConstantRingMap (T := Y) φ
  let P : proEtaleRingModules Y (proEtaleConstantRing Y A) ⥤
      PresheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing Y B)).obj :=
    { obj := fun M ↦ SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a M
      map := fun {M N} h ↦
        { app := fun U ↦ (ModuleCat.extendScalars (a.hom.app U).hom).map (h.val.app U)
          naturality := SheafOfModules.changeOfRingsHom_naturality a _ h }
      map_id := fun M ↦ by
        ext U : 1
        exact (ModuleCat.extendScalars (a.hom.app U).hom).map_id _
      map_comp := fun h k ↦ by
        ext U : 1
        exact (ModuleCat.extendScalars (a.hom.app U).hom).map_comp _ _ }
  exact P ⋙ PresheafOfModules.sheafification (𝟙 _)

private def scalarBalancingAdjunction
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (Y : Scheme.{u}) :
    scalarBalancingExtension φ Y ⊣ scalarMateRestriction φ Y :=
  SheafOfModules.CoefficientOrdinaryProof.tensorAdjunction
    (proEtaleConstantRingMap (T := Y) φ)

private theorem scalarBalancingAdjunction_unit
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (Y : Scheme.{u})
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (U : Y.ProEtᵒᵖ)
    (x : M.val.obj U) :
    ((scalarBalancingAdjunction φ Y).unit.app M).val.app U x =
      scalarMateTensorSection φ Y M U 1 x := by
  rw [← Adjunction.homEquiv_id]
  rfl

private theorem scalarTensor_hom_ext (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {M N H : proEtaleRingModules X R}
    (v w : ((proEtaleOrdinaryTensor X R).obj M).obj N ⟶ H)
    (h : ∀ (U : X.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      v.val.app U (proEtaleTensorPair X R M N U x y) =
        w.val.app U (proEtaleTensorPair X R M N U x y)) : v = w := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv _ H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  ext z
  change v.val.app U ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
      ((adj.unit.app (M.val ⊗ N.val)).app U z)) =
    w.val.app U ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
      ((adj.unit.app (M.val ⊗ N.val)).app U z))
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => exact h U x y
  | add z z' hz hz' => simp only [map_add, hz, hz']

private theorem scalarSection_toSheafify
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (Y : Scheme.{u})
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (U : Y.ProEtᵒᵖ)
    (b : (proEtaleConstantRing Y B).obj.obj U) (x : M.val.obj U) :
    scalarMateTensorSection φ Y M U b x =
      (toSheafify (ProEt.topology Y)
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
          (proEtaleConstantRingMap (T := Y) φ) M).presheaf).app U
        (b ⊗ₜ[_, ((proEtaleConstantRingMap (T := Y) φ).hom.app U).hom] x) := by
  have h := PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
    (J := ProEt.topology Y)
    (𝟙 ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y B)).obj)
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      (proEtaleConstantRingMap (T := Y) φ) M)
  exact congrArg (fun q ↦ q.app U
    (b ⊗ₜ[_, ((proEtaleConstantRingMap (T := Y) φ).hom.app U).hom] x)) h

private theorem scalarSection_map
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (Y : Scheme.{u})
    {M N : proEtaleRingModules Y (proEtaleConstantRing Y A)} (v : M ⟶ N)
    (U : Y.ProEtᵒᵖ) (b : (proEtaleConstantRing Y B).obj.obj U) (x : M.val.obj U) :
    ((scalarBalancingExtension φ Y).map v).val.app U
      (scalarMateTensorSection φ Y M U b x) =
        scalarMateTensorSection φ Y N U b (v.val.app U x) := by
  let a := proEtaleConstantRingMap (T := Y) φ
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y B)).obj)
  let q : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a N :=
    { app := fun V ↦ (ModuleCat.extendScalars (a.hom.app V).hom).map (v.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality a M v }
  exact (congrArg (fun k ↦ k.app U (b ⊗ₜ[_, (a.hom.app U).hom] x))
    (adj.unit.naturality q)).symm

private def scalarTensorComponent
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (Y : Scheme.{u})
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    (scalarMateOrdinaryTensor φ Y).obj M ≅
      (scalarMateRestriction φ Y).obj ((scalarBalancingExtension φ Y).obj M) := by
  letI := SheafOfModules.monoidalCategory (proEtaleConstantRing Y A)
  letI := SheafOfModules.symmetricCategory (proEtaleConstantRing Y A)
  exact (BraidedCategory.braiding M (scalarMateCoefficient φ Y)) ≪≫
    (SheafOfModules.IndependentExtensionTensor.exists_extensionTensorComparison
      (proEtaleConstantRingMap (T := Y) φ) M).choose

private theorem scalarTensorComponent_pure
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (Y : Scheme.{u})
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (U : Y.ProEtᵒᵖ)
    (x : M.val.obj U) (b : (proEtaleConstantRing Y B).obj.obj U) :
    (scalarTensorComponent φ Y M).hom.val.app U
      (proEtaleTensorPair Y (proEtaleConstantRing Y A) M
        (scalarMateCoefficient φ Y) U x b) = scalarMateTensorSection φ Y M U b x := by
  let := SheafOfModules.monoidalCategory (proEtaleConstantRing Y A)
  let := SheafOfModules.symmetricCategory (proEtaleConstantRing Y A)
  have he := (SheafOfModules.IndependentExtensionTensor.exists_extensionTensorComparison
    (proEtaleConstantRingMap (T := Y) φ) M).choose_spec U b x
  have hb := CategoryTheory.CochainPullback.moduleTmul_braiding M
    (scalarMateCoefficient φ Y) U x b
  change ((SheafOfModules.IndependentExtensionTensor.exists_extensionTensorComparison
    (proEtaleConstantRingMap (T := Y) φ) M).choose).hom.val.app U
      ((BraidedCategory.braiding M (scalarMateCoefficient φ Y)).hom.val.app U
        (proEtaleTensorPair Y (proEtaleConstantRing Y A) M
          (scalarMateCoefficient φ Y) U x b)) = _
  rw [show (BraidedCategory.braiding M (scalarMateCoefficient φ Y)).hom.val.app U
      (proEtaleTensorPair Y (proEtaleConstantRing Y A) M
        (scalarMateCoefficient φ Y) U x b) =
      proEtaleTensorPair Y (proEtaleConstantRing Y A) (scalarMateCoefficient φ Y) M U b x
        from hb]
  rw [scalarSection_toSheafify]
  exact he

private theorem scalarTensorComponent_naturality
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (Y : Scheme.{u})
    {M N : proEtaleRingModules Y (proEtaleConstantRing Y A)} (v : M ⟶ N) :
    (scalarMateOrdinaryTensor φ Y).map v ≫ (scalarTensorComponent φ Y N).hom =
      (scalarTensorComponent φ Y M).hom ≫
        (scalarMateRestriction φ Y).map ((scalarBalancingExtension φ Y).map v) := by
  apply scalarTensor_hom_ext Y (proEtaleConstantRing Y A)
  intro U x b
  have ht := CategoryTheory.CochainPullback.moduleTmul_map v
    (𝟙 (scalarMateCoefficient φ Y)) U x b
  simp only [MonoidalCategory.tensorHom_id, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply] at ht
  change (scalarTensorComponent φ Y N).hom.val.app U
      (((scalarMateOrdinaryTensor φ Y).map v).val.app U
        (proEtaleTensorPair Y (proEtaleConstantRing Y A) M
          (scalarMateCoefficient φ Y) U x b)) =
    ((scalarBalancingExtension φ Y).map v).val.app U
      ((scalarTensorComponent φ Y M).hom.val.app U
        (proEtaleTensorPair Y (proEtaleConstantRing Y A) M
          (scalarMateCoefficient φ Y) U x b))
  rw [show (((scalarMateOrdinaryTensor φ Y).map v).val.app U)
      (proEtaleTensorPair Y (proEtaleConstantRing Y A) M
        (scalarMateCoefficient φ Y) U x b) =
      proEtaleTensorPair Y (proEtaleConstantRing Y A) N
        (scalarMateCoefficient φ Y) U (v.val.app U x) b from ht]
  rw [scalarTensorComponent_pure, scalarTensorComponent_pure, scalarSection_map]

/-- Restricted concrete scalar extension is uniquely the ordinary tensor functor.
Source: Stacks 03EK (blueprint: lem-sp-proetale-concrete-scalar-extension).
Proof: restriction commutes with sheafification. Swap the two factors of the
sectionwise tensor product and sheafify. The swap is natural on module maps and
sends b tensor x to x tensor b. Pure tensors determine every map out of a sheaf
 tensor product by the sheafification adjunction, proving uniqueness. -/
theorem scalarBalancingTensorIso_existsUnique
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (Y : Scheme.{u}) :
    ∃! e : scalarBalancingExtension φ Y ⋙ scalarMateRestriction φ Y ≅
        scalarMateOrdinaryTensor φ Y,
      ∀ (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (U : Y.ProEtᵒᵖ)
        (b : (proEtaleConstantRing Y B).obj.obj U) (x : M.val.obj U),
        (e.hom.app M).val.app U (scalarMateTensorSection φ Y M U b x) =
          proEtaleTensorPair Y (proEtaleConstantRing Y A) M
            (scalarMateCoefficient φ Y) U x b := by
  let c : scalarMateOrdinaryTensor φ Y ≅
      scalarBalancingExtension φ Y ⋙ scalarMateRestriction φ Y :=
    NatIso.ofComponents (scalarTensorComponent φ Y)
      (fun h ↦ scalarTensorComponent_naturality φ Y h)
  let e := c.symm
  have he : ∀ M U b x, (e.hom.app M).val.app U
      (scalarMateTensorSection φ Y M U b x) =
      proEtaleTensorPair Y (proEtaleConstantRing Y A) M
        (scalarMateCoefficient φ Y) U x b := by
    intro M U b x
    rw [← scalarTensorComponent_pure φ Y M U x b]
    exact congrArg (fun h ↦ h.val.app U
      (proEtaleTensorPair Y (proEtaleConstantRing Y A) M
        (scalarMateCoefficient φ Y) U x b)) (c.hom_inv_id_app M)
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (cancel_epi (e.inv.app M)).mp
  apply scalarTensor_hom_ext Y (proEtaleConstantRing Y A)
  intro U x b
  have hinv : (e.inv.app M).val.app U
      (proEtaleTensorPair Y (proEtaleConstantRing Y A) M
        (scalarMateCoefficient φ Y) U x b) = scalarMateTensorSection φ Y M U b x := by
    rw [← he]
    exact congrArg (fun h ↦ h.val.app U (scalarMateTensorSection φ Y M U b x))
      (e.hom_inv_id_app M)
  change (e'.hom.app M).val.app U ((e.inv.app M).val.app U _) =
    (e.hom.app M).val.app U ((e.inv.app M).val.app U _)
  rw [hinv]
  exact (he' M U b x).trans (he M U b x).symm

/-- The uniquely normalized tensor comparison for the concrete change-of-rings functor.
Source: Stacks 03EK (blueprint: lem-sp-proetale-concrete-scalar-extension). -/
def scalarBalancingTensorIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (Y : Scheme.{u}) :=
  (scalarBalancingTensorIso_existsUnique φ Y).exists.choose

private noncomputable def scalarExtensionComparison
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarBalancingExtension φ Y ⋙
        proEtaleConstantRingPullback B f ≅
      proEtaleConstantRingPullback A f ⋙
        scalarBalancingExtension φ X := by
  let d := proEtaleRingRestrictionDirectImage f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm
  let a := ((scalarBalancingAdjunction φ Y).comp
    (proEtaleConstantRingAdjunction B f)).ofNatIsoRight d
  let b := (proEtaleConstantRingAdjunction A f).comp
    (scalarBalancingAdjunction φ X)
  exact a.leftAdjointUniq b

private theorem scalarExtensionComparison_unit
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (V : Y.ProEt)
    (x : M.val.obj (Opposite.op V)) :
    ((scalarExtensionComparison φ f).hom.app M).val.app
        (Opposite.op ((proEtaleBaseChange f).obj V))
        (((proEtaleConstantRingAdjunction B f).unit.app _).val.app (Opposite.op V)
          (scalarMateTensorSection φ Y
            M (Opposite.op V) 1 x)) =
      scalarMateTensorSection φ X
        ((proEtaleConstantRingPullback A f).obj M)
        (Opposite.op ((proEtaleBaseChange f).obj V)) 1
        (((proEtaleConstantRingAdjunction A f).unit.app M).val.app (Opposite.op V) x) := by
  let d := proEtaleRingRestrictionDirectImage f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm
  let a := ((scalarBalancingAdjunction φ Y).comp
    (proEtaleConstantRingAdjunction B f)).ofNatIsoRight d
  let b := (proEtaleConstantRingAdjunction A f).comp
    (scalarBalancingAdjunction φ X)
  have he := a.homEquiv_leftAdjointUniq_hom_app b M
  simp only [a, Adjunction.homEquiv_ofNatIsoRight_apply] at he
  have hx := congrArg (fun h ↦ h.val.app (Opposite.op V) x) he
  have hd (Q : proEtaleRingModules X (proEtaleConstantRing X B))
      (z : Q.val.obj (Opposite.op ((proEtaleBaseChange f).obj V))) :
      (d.hom.app Q).val.app (Opposite.op V) z = z := by
    exact (Classical.choose_spec
      (proEtaleRingRestrictionDirectImage_existsUnique f
        (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
        (proEtaleConstantRing X A) (proEtaleConstantRing X B)
        (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
        (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
        (proEtaleConstantInverseImageMap_naturality f
          (CommRingCat.ofHom (RingHom.ulift φ))).symm)).1 Q (Opposite.op V) z
  change (d.hom.app _).val.app (Opposite.op V)
    (((scalarBalancingAdjunction φ Y).homEquiv M _
      ((proEtaleConstantRingAdjunction B f).homEquiv _ _
        ((scalarExtensionComparison φ f).hom.app M))).val.app (Opposite.op V) x) = _ at hx
  rw [hd, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit] at hx
  change ((scalarExtensionComparison φ f).hom.app M).val.app
      (Opposite.op ((proEtaleBaseChange f).obj V))
      (((proEtaleConstantRingAdjunction B f).unit.app _).val.app (Opposite.op V)
        (((scalarBalancingAdjunction φ Y).unit.app M).val.app (Opposite.op V) x)) =
    ((scalarBalancingAdjunction φ X).unit.app
      ((proEtaleConstantRingPullback A f).obj M)).val.app
        (Opposite.op ((proEtaleBaseChange f).obj V))
        (((proEtaleConstantRingAdjunction A f).unit.app M).val.app (Opposite.op V) x) at hx
  rw [scalarBalancingAdjunction_unit, scalarBalancingAdjunction_unit] at hx
  exact hx

private theorem scalarTensorIso_section
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (Y : Scheme.{u})
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (U : Y.ProEtᵒᵖ)
    (b : (proEtaleConstantRing Y B).obj.obj U) (x : M.val.obj U) :
    ((scalarBalancingTensorIso φ Y).hom.app M).val.app U
      (scalarMateTensorSection φ Y M U b x) =
        proEtaleTensorPair Y (proEtaleConstantRing Y A) M
          (scalarMateCoefficient φ Y) U x b := by
  exact (scalarBalancingTensorIso_existsUnique φ Y).exists.choose_spec M U b x

private theorem scalarSection_smul
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (Y : Scheme.{u})
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (U : Y.ProEtᵒᵖ)
    (b : (proEtaleConstantRing Y B).obj.obj U) (x : M.val.obj U) :
    scalarMateTensorSection φ Y M U b x =
      b • scalarMateTensorSection φ Y M U 1 x := by
  let oneB : (proEtaleConstantRing Y B).obj.obj U := 1
  let a := proEtaleConstantRingMap (T := Y) φ
  let η := ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (R := (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y B))
    (𝟙 _)).unit.app (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a M)).app U
  change η (b ⊗ₜ[_, (a.hom.app U).hom] x) =
    b • η (oneB ⊗ₜ[_, (a.hom.app U).hom] x)
  have ht := ModuleCat.ExtendScalars.smul_tmul (a.hom.app U).hom b oneB x
  have hη := η.hom.map_smul b (oneB ⊗ₜ[_, (a.hom.app U).hom] x)
  simpa only [oneB, mul_one] using (congrArg η ht.symm).trans hη

private theorem scalarExtensionComparison_section
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (V : Y.ProEt)
    (x : M.val.obj (Opposite.op V))
    (s : (proEtaleConstantRing Y B).obj.obj (Opposite.op V)) :
    ((scalarExtensionComparison φ f).hom.app M).val.app
        (Opposite.op ((proEtaleBaseChange f).obj V))
        (((proEtaleConstantRingAdjunction B f).unit.app _).val.app (Opposite.op V)
          (scalarMateTensorSection φ Y
            M (Opposite.op V) s x)) =
      scalarMateTensorSection φ X
        ((proEtaleConstantRingPullback A f).obj M)
        (Opposite.op ((proEtaleBaseChange f).obj V))
        ((proEtaleRingDirectImageMap f (proEtaleConstantRing Y B)
          (proEtaleConstantRing X B) (proEtaleConstantRingComparison f B)).hom.app
            (Opposite.op V) s)
        (((proEtaleConstantRingAdjunction A f).unit.app M).val.app (Opposite.op V) x) := by
  rw [scalarSection_smul φ Y M (Opposite.op V) s x, map_smul]
  change ((scalarExtensionComparison φ f).hom.app M).val.app
      (Opposite.op ((proEtaleBaseChange f).obj V))
      (((proEtaleRingDirectImageMap f (proEtaleConstantRing Y B)
        (proEtaleConstantRing X B) (proEtaleConstantRingComparison f B)).hom.app
          (Opposite.op V) s) • _) = _
  rw [map_smul, scalarExtensionComparison_unit]
  exact (scalarSection_smul φ X _ _ _ _).symm

private theorem scalarExtensionBalancing_linear
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (W : X.ProEtᵒᵖ)
    (b : (proEtaleConstantRing X B).obj.obj W)
    (h : ((proEtaleConstantRingPullback B f).obj
      ((scalarBalancingExtension φ Y).obj M)).val.obj W) :
    (scalarBalancingMap φ f (scalarExtensionBalancing φ f) M).val.app W (b • h) =
      b • (@id (((scalarBalancingExtension φ X).obj
        ((proEtaleConstantRingPullback A f).obj M)).val.obj W)
          ((scalarBalancingMap φ f (scalarExtensionBalancing φ f) M).val.app W h)) := by
  have he : scalarBalancingMap φ f (scalarExtensionBalancing φ f) M =
      (scalarMateRestriction φ X).map ((scalarExtensionComparison φ f).hom.app M) := by
    simp [scalarBalancingMap, scalarExtensionBalancing, Category.assoc]
  rw [he]
  exact (((scalarExtensionComparison φ f).hom.app M).val.app W).hom.map_smul b h

private theorem scalarUnitPullback_section
    (B : Type u) [CommRing B] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.ProEt) (s : (proEtaleConstantRing Y B).obj.obj (Opposite.op V)) :
    (scalarMateUnitPullback B f).hom.val.app
        (Opposite.op ((proEtaleBaseChange f).obj V))
        (((proEtaleConstantRingAdjunction B f).unit.app
          (scalarMateUnit B Y)).val.app (Opposite.op V) s) =
      (proEtaleRingDirectImageMap f (proEtaleConstantRing Y B)
        (proEtaleConstantRing X B) (proEtaleConstantRingComparison f B)).hom.app
          (Opposite.op V) s := by
  let R := proEtaleConstantRing Y B
  let S := proEtaleConstantRing X B
  let c := proEtaleConstantRingComparison f B
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let adj := proEtaleRingModuleAdjunction f R S c
  let φ : (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) :=
    ⟨Functor.whiskerRight (proEtaleRingDirectImageMap f R S c).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint := adj.isRightAdjoint
  let adj' := SheafOfModules.pullbackPushforwardAdjunction.{u + 1} φ
  let e := adj.leftAdjointUniq adj'
  let j := e.app (SheafOfModules.unit _) ≪≫
    asIso (SheafOfModules.pullbackObjUnitToUnit φ)
  have hj : adj.homEquiv _ _ j.hom = SheafOfModules.unitToPushforwardObjUnit φ := by
    change adj.homEquiv _ _ (e.hom.app _ ≫ _) = _
    rw [adj.homEquiv_naturality_right]
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit φ
  have hcompat (M : proEtaleRingModules Y R) :
      (proEtaleOrdinaryTensorPullback f R S c M (𝟙_ _)).hom ≫
        (𝟙 _ ⊗ₘ j.hom) ≫ (ρ_ _).hom =
      (proEtaleRingModulePullback f R S c).map (ρ_ M).hom := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, adj.unit_naturality]
    apply proEtaleTensorPair_hom_ext Y R
    intro U m r
    obtain ⟨U⟩ := U
    have hmu := (Classical.choose_spec
      (proEtaleOrdinaryTensorPullback_existsUnique f R S c).exists).2 M (𝟙_ _) U m r
    have hjr := congrArg (fun z ↦ z.val.app (Opposite.op U) r) hj
    rw [Adjunction.homEquiv_unit] at hjr
    change j.hom.val.app (Opposite.op ((proEtaleBaseChange f).obj U))
      ((adj.unit.app (𝟙_ _)).val.app (Opposite.op U) r) =
        (proEtaleRingDirectImageMap f R S c).hom.app (Opposite.op U) r at hjr
    change (ρ_ ((proEtaleRingModulePullback f R S c).obj M)).hom.val.app _
        (((SheafOfModules.monoidalCategory S).tensorHom (𝟙 _) j.hom).val.app _
          ((proEtaleOrdinaryTensorPullback f R S c M (𝟙_ _)).hom.val.app _
            ((adj.unit.app _).val.app _ (proEtaleTensorPair Y R M (𝟙_ _) _ m r)))) =
      (adj.unit.app M).val.app _ ((ρ_ M).hom.val.app _
        (proEtaleTensorPair Y R M (𝟙_ _) _ m r))
    erw [hmu]
    let V := Opposite.op ((proEtaleBaseChange f).obj U)
    let m' : ((proEtaleRingModulePullback f R S c).obj M).val.obj V :=
      (adj.unit.app M).val.app (Opposite.op U) m
    let r' : ((proEtaleRingModulePullback f R S c).obj (𝟙_ _)).val.obj V :=
      (adj.unit.app (𝟙_ _)).val.app (Opposite.op U) r
    change j.hom.val.app V r' =
      (proEtaleRingDirectImageMap f R S c).hom.app (Opposite.op U) r at hjr
    change (ρ_ ((proEtaleRingModulePullback f R S c).obj M)).hom.val.app V
        (((SheafOfModules.monoidalCategory S).tensorHom (𝟙 _) j.hom).val.app V
          (proEtaleTensorPair X S _ _ V m' r')) = _
    have htens := proEtaleTensorPair_tensorHom X S
      (𝟙 ((proEtaleRingModulePullback f R S c).obj M)) j.hom V m' r'
    change ((SheafOfModules.monoidalCategory S).tensorHom (𝟙 _) j.hom).val.app V
        (proEtaleTensorPair X S _ _ V m' r') =
      proEtaleTensorPair X S _ _ V m' (j.hom.val.app V r') at htens
    calc
      _ = (ρ_ ((proEtaleRingModulePullback f R S c).obj M)).hom.val.app V
          (proEtaleTensorPair X S _ _ V m' (j.hom.val.app V r')) :=
        congrArg (fun z ↦
          (ρ_ ((proEtaleRingModulePullback f R S c).obj M)).hom.val.app V z) htens
      _ = (j.hom.val.app V r') • m' :=
        proEtaleTensorPair_rightUnitor X S _ V m' (j.hom.val.app V r')
      _ = ((proEtaleRingDirectImageMap f R S c).hom.app (Opposite.op U) r) • m' :=
        congrArg (fun z ↦ z • m') hjr
      _ = (adj.unit.app M).val.app (Opposite.op U) (r • m) :=
        ((adj.unit.app M).val.app (Opposite.op U)).hom.map_smul r m |>.symm
      _ = _ := congrArg (fun z ↦ (adj.unit.app M).val.app (Opposite.op U) z)
        (proEtaleTensorPair_rightUnitor Y R M (Opposite.op U) m r).symm
  have heq : scalarMateUnitPullback B f = j :=
    (proEtaleProjectionUnit_existsUnique f R S c).unique
      (Classical.choose_spec (proEtaleProjectionUnit_existsUnique f R S c).exists) hcompat
  rw [heq]
  have hjr := congrArg (fun z ↦ z.val.app (Opposite.op V) s) hj
  rw [Adjunction.homEquiv_unit] at hjr
  exact hjr

private noncomputable def canonicalTensorBalancing {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarMateOrdinaryTensor φ Y ⋙ proEtaleConstantRingPullback A f ≅
      proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ X := by
  let F := proEtaleConstantRingPullback A f
  let q₀ := scalarMateCoefficientPullback φ f
  let q : F.obj (scalarMateCoefficient φ Y) ≅ scalarMateCoefficient φ X :=
    eqToIso (by rfl) ≪≫ q₀
  let h : ∀ M : proEtaleRingModules Y (proEtaleConstantRing Y A),
      (F.obj ((scalarMateOrdinaryTensor φ Y).obj M)) ≅
        (scalarMateOrdinaryTensor φ X).obj (F.obj M) := fun M ↦
    (proEtaleOrdinaryTensorPullback f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A)
      M (scalarMateCoefficient φ Y)).trans
      (Functor.mapIso ((proEtaleOrdinaryTensor X (proEtaleConstantRing X A)).obj (F.obj M)) q)
  exact NatIso.ofComponents h (by
    intro M N k
    dsimp [h, F, q, q₀]
    have hn := proEtaleOrdinaryTensorPullback_naturality f
      (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
      (proEtaleConstantRingComparison f A) M N
      (scalarMateCoefficient φ Y) (scalarMateCoefficient φ Y) k (𝟙 _)
    have hq := ((proEtaleOrdinaryTensor X (proEtaleConstantRing X A)).map
      (F.map k)).naturality q.hom
    have hq' :
        MonoidalCategoryStruct.whiskerRight (F.map k)
            (F.obj (scalarMateCoefficient φ Y)) ≫
          ((proEtaleOrdinaryTensor X (proEtaleConstantRing X A)).obj
            (F.obj N)).map q.hom =
        ((proEtaleOrdinaryTensor X (proEtaleConstantRing X A)).obj
            (F.obj M)).map q.hom ≫
          MonoidalCategoryStruct.whiskerRight (F.map k)
            (scalarMateCoefficient φ X) := by
      simpa using hq.symm
    calc
      _ = (proEtaleOrdinaryTensorPullback f (proEtaleConstantRing Y A)
          (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A)
          M (scalarMateCoefficient φ Y)).hom ≫
          MonoidalCategoryStruct.whiskerRight (F.map k)
            (F.obj (scalarMateCoefficient φ Y)) ≫
          ((proEtaleOrdinaryTensor X (proEtaleConstantRing X A)).obj (F.obj N)).map
            q.hom := by
        have hn' := congrArg (fun z ↦ z ≫
          ((proEtaleOrdinaryTensor X (proEtaleConstantRing X A)).obj
            (F.obj N)).map q.hom) hn
        simpa [F, q, q₀, Functor.map_id, Functor.map_comp, Category.assoc] using hn'
      _ = (proEtaleOrdinaryTensorPullback f (proEtaleConstantRing Y A)
          (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A)
          M (scalarMateCoefficient φ Y)).hom ≫
          ((proEtaleOrdinaryTensor X (proEtaleConstantRing X A)).obj (F.obj M)).map
            q.hom ≫
          MonoidalCategoryStruct.whiskerRight (F.map k)
            (scalarMateCoefficient φ X) := by
        rw [hq']
      _ = _ := by simp [F, q, q₀, Category.assoc]
    )


section TotalComparison

universe v u' v'

attribute [local implicit_reducible] CategoryTheory.Functor.mapHomologicalComplex

private theorem collapse_ι {M : Type*} [Category* M] [Preadditive M] [HasZeroObject M]
    (T : M ⥤ M ⥤ M) [T.Additive] [∀ X, (T.obj X).Additive]
    [∀ A B : CochainComplex M ℤ, CochainComplex.HasMapBifunctor A B T]
    (L : M) (E : CochainComplex M ℤ) (i : ℤ) :
    HomologicalComplex.ιMapBifunctor E ((CochainComplex.singleFunctor _ 0).obj L)
        T (.up ℤ) i 0 i (Int.add_zero i) ≫
      (CochainComplex.mapBifunctorSingle₂Iso T L E).hom.f i =
        (T.obj (E.X i)).map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).hom := by
  dsimp [CochainComplex.mapBifunctorSingle₂Iso, CochainComplex.mapBifunctorSingle₁Iso,
    HomologicalComplex.Hom.isoOfComponents]
  erw [HomologicalComplex.ι_mapBifunctorFlipIso_inv_assoc]
  simp [CochainComplex.mapBifunctorSingle₁XIso, HomologicalComplex.singleObjXSelf]

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [MonoidalCategory B]
  [MonoidalPreadditive A] [MonoidalPreadditive B]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B]
  (L : A ⥤ B) [L.Additive]
  (e : ∀ X Y : A, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)
  (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
    L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
  (C : A) (D : B) (q : L.obj C ≅ D)
  (t : tensorRight C ⋙ L ≅ L ⋙ tensorRight D)
  (ht : ∀ M, t.hom.app M = (e M C).hom ≫ (L.obj M ◁ q.hom))

include ht in
private theorem total_single (P : CochainComplex A ℤ) :
    tensorPullbackTotal L e he P ((CochainComplex.singleFunctor A 0).obj C) ≫
      (L.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor A) C P).hom ≫
      (NatTrans.mapHomologicalComplex t.hom (.up ℤ)).app P =
    HomologicalComplex.mapBifunctorMap
      (𝟙 ((L.mapHomologicalComplex (.up ℤ)).obj P))
      (((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).app C).hom ≫
        (CochainComplex.singleFunctor B 0).map q.hom)
      (curriedTensor B) (.up ℤ) ≫
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor B) D
        ((L.mapHomologicalComplex (.up ℤ)).obj P)).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  by_cases hb : b = 0
  · subst b
    have ha : a = n := by simpa using hab
    subst a
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplex_map_f, ht]
    dsimp only [tensorPullbackTotal]
    simp only [tensorPullbackTotalComponent, HomologicalComplex.ι_mapBifunctorDesc_assoc]
    simp only [Category.assoc]
    rw [← L.map_comp_assoc, collapse_ι]
    rw [HomologicalComplex.ι_mapBifunctorMap_assoc, collapse_ι]
    dsimp only [curriedTensor, Functor.mapHomologicalComplex_obj_X]
    simp only [HomologicalComplex.id_f, id_whiskerRight, Category.id_comp]
    have hn := he (𝟙 (P.X n))
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 C).hom
    simp only [tensorHom_def, id_whiskerRight, Category.id_comp] at hn
    erw [reassoc_of% hn, Iso.inv_hom_id_assoc]
    with_unfolding_all
      simp only [← whiskerLeft_comp, HomologicalComplex.comp_f, CochainComplex.singleFunctor,
        CochainComplex.singleFunctors, Iso.app_hom,
        HomologicalComplex.single_map_f_self,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Category.assoc,
        Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    erw [L.map_id, id_whiskerRight, Category.id_comp]
    rfl
  · apply IsZero.eq_of_src
    exact Functor.map_isZero ((curriedTensor B).obj (L.obj (P.X a)))
      (L.map_isZero (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 C b hb))

end TotalComparison

end AlgebraicGeometry.ProEtale
