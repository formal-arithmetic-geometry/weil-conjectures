/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge
public import Sheaf.AlgebraicGeometry.AffineCohomologyComparisonData
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import WeilConjectures.AlgebraicGeometry.BasicPropertiesLinearity
import WeilConjectures.AlgebraicGeometry.BasicPropertiesIdentity
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf

/-! # Transport of a natural affine structural cohomology comparison -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
section Construction
attribute [local irreducible] RingedSpace.moduleCohomology tensorPullback tensorPullbackObj
  moduleCohomologyFMap tensorPullbackObjUnitToUnit tensorSectionsUnit tensorSectionsComp
  tensorPullbackSectionAdjunction tensorPullbackSectionComp Functor.rightDerived
  Functor.rightDerivedToHomotopyCategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local reducible] TopCat.Sheaf TopCat.instCategorySheaf
  topDegreeCohomologyOnBase Scheme.Modules Scheme.Modules.Hom
  Scheme.Modules.instCategory Scheme.Modules.instAbelian

attribute [local instance 2000] topDegreeModuleCategory topDegreeModulePreadditive
  topDegreeModuleAbelian
set_option allowUnsafeReducibility true in
attribute [local reducible] topDegreeModuleCategory topDegreeModulePreadditive
  topDegreeModuleAbelian

/-- Canonical structural-unit cohomology transport component.
Source: Stacks, Tags 01F8, 01FB, 0096 and 0097.
(blueprint: new-unit-affine-symmetry). -/
abbrev unitAffineH (X : Scheme.{u}) (q : ℕ) : AddCommGrpCat.{u} :=
  (forget₂ _ AddCommGrpCat).obj
    ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
      (SheafOfModules.unit X.ringCatSheaf))

instance unitAffineCohomModule (X : Scheme.{u}) (q : ℕ) (M : X.Modules) :
    Module Γ(X, ⊤) ((RingedSpace.moduleCohomology X.toRingedSpace q).obj M) :=
  inferInstanceAs (Module ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
    ((RingedSpace.moduleCohomology X.toRingedSpace q).obj M))

instance unitAffineForgetCohomModule (X : Scheme.{u}) (q : ℕ) (M : X.Modules) :
    Module Γ(X, ⊤) ((forget₂ _ AddCommGrpCat).obj
      ((RingedSpace.moduleCohomology X.toRingedSpace q).obj M)) :=
  unitAffineCohomModule X q M

instance unitAffineHModule (X : Scheme.{u}) (q : ℕ) : Module Γ(X, ⊤) (unitAffineH X q) :=
  unitAffineCohomModule X q _

instance unitAffineForgetModule {R : Type u} [Ring R] (M : ModuleCat.{u} R) :
    Module R ((forget₂ _ AddCommGrpCat).obj M) := ModuleCat.isModule M

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance unitAffineSectionsModule (Y : Scheme.{u}) (M : Y.Modules) :
    Module Γ(Y, ⊤) ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj M) :=
  ModuleCat.isModule ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj M)

attribute [local instance 3000] unitAffineSectionsModule unitAffineCohomModule
  unitAffineForgetCohomModule unitAffineHModule unitAffineForgetModule

/-- Evaluation at the whole scheme, viewed as the group of global sections.
Source: Stacks, Tag 01DZ (blueprint: new-unit-affine-symmetry). -/
def unitAffineSectionsEquiv (Y : Scheme.{u}) (M : Y.Modules) :
    (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj M ≃+ Γ(M, ⊤) :=
  AddEquiv.refl _

/-- The evaluation identification preserves multiplication by a global function.
Source: Stacks, Tag 01DZ (blueprint: new-unit-affine-symmetry). -/
theorem unitAffineSectionsEquiv_smul (Y : Scheme.{u}) (M : Y.Modules)
    (a : Γ(Y, ⊤)) (x : (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj M) :
    unitAffineSectionsEquiv Y M (a • x) = a • unitAffineSectionsEquiv Y M x := by
  rfl

/-- Canonical structural-unit cohomology transport component.
Source: Stacks, Tags 01F8, 01FB, 0096 and 0097.
(blueprint: new-unit-affine-symmetry). -/
def unitAffineHMap {X Y : Scheme.{u}} (h : X ⟶ Y) (q : ℕ) : unitAffineH Y q ⟶ unitAffineH X q :=
  moduleCohomologyFMap h (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) q

theorem unitAffineHMap_comp {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z) (q : ℕ) :
    unitAffineHMap (h ≫ k) q = unitAffineHMap k q ≫ unitAffineHMap h q := by
  have hc : SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom ≫
      (pushforward k).map (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) ≫
        (pushforwardComp h k).hom.app (SheafOfModules.unit X.ringCatSheaf) =
      SheafOfModules.unitToPushforwardObjUnit (h ≫ k).toRingCatSheafHom := by
    ext U
    rfl
  exact (congrArg (fun a ↦ moduleCohomologyFMap (h ≫ k) a q) hc).symm.trans
    (moduleCohomologyFMap_comp h k _ _ q)

theorem unitAffineHMap_id (X : Scheme.{u}) (q : ℕ) :
    unitAffineHMap (𝟙 X) q = 𝟙 (unitAffineH X q) := by
  have he : SheafOfModules.unitToPushforwardObjUnit (𝟙 X : X ⟶ X).toRingCatSheafHom =
      𝟙 (SheafOfModules.unit X.ringCatSheaf) := by
    ext U
    rfl
  unfold unitAffineHMap
  rw [he, moduleCohomologyFMap_basic_identity]
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

/-- Canonical structural-unit cohomology transport component.
Source: Stacks, Tags 01F8, 01FB, 0096 and 0097.
(blueprint: new-unit-affine-symmetry). -/
def unitAffineHIso {X Y : Scheme.{u}} (i : X ≅ Y) (q : ℕ) : unitAffineH Y q ≅ unitAffineH X q where
  hom := unitAffineHMap i.hom q
  inv := unitAffineHMap i.inv q
  hom_inv_id := by rw [← unitAffineHMap_comp, i.inv_hom_id, unitAffineHMap_id]
  inv_hom_id := by rw [← unitAffineHMap_comp, i.hom_inv_id, unitAffineHMap_id]

/-- Canonical structural-unit cohomology transport component.
Source: Stacks, Tags 01F8, 01FB, 0096 and 0097.
(blueprint: new-unit-affine-symmetry). -/
def unitAffineCoefficientIso {X Y : Scheme.{u}} (h : X ⟶ Y) :
    (tensorPullback h).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  letI := (tensorPullbackObjUnitToUnit_isIso h).1
  exact asIso (tensorPullbackObjUnitToUnit h)

/-- Canonical structural-unit cohomology transport component.
Source: Stacks, Tags 01F8, 01FB, 0096 and 0097.
(blueprint: new-unit-affine-symmetry). -/
def unitAffineCoefficientH {X Y : Scheme.{u}} (h : X ⟶ Y) (q : ℕ) :
    (forget₂ _ AddCommGrpCat).obj
      ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
        ((tensorPullback h).obj (SheafOfModules.unit Y.ringCatSheaf))) ≅ unitAffineH X q :=
  (forget₂ _ AddCommGrpCat).mapIso
    ((RingedSpace.moduleCohomology X.toRingedSpace q).mapIso (unitAffineCoefficientIso h))

private theorem unitCoefficientH_hom_smul {X Y : Scheme.{u}} (h : X ⟶ Y) (q : ℕ)
    (a : Γ(X, ⊤))
    (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj
      ((tensorPullback h).obj (SheafOfModules.unit Y.ringCatSheaf))) :
    (unitAffineCoefficientH h q).hom (a • x) = a • (unitAffineCoefficientH h q).hom x := by
  exact ((RingedSpace.moduleCohomology X.toRingedSpace q).map
    (unitAffineCoefficientIso h).hom).hom.map_smul a x

private theorem unitCoefficientH_inv_smul {X Y : Scheme.{u}} (h : X ⟶ Y) (q : ℕ)
    (a : Γ(X, ⊤)) (x : unitAffineH X q) :
    (unitAffineCoefficientH h q).inv (a • x) = a • (unitAffineCoefficientH h q).inv x := by
  exact ((RingedSpace.moduleCohomology X.toRingedSpace q).map
    (unitAffineCoefficientIso h).inv).hom.map_smul a x

attribute [local irreducible] unitAffineCoefficientH unitAffineCoefficientIso

/-- Canonical structural-unit cohomology transport component.
Source: Stacks, Tags 01F8, 01FB, 0096 and 0097.
(blueprint: new-unit-affine-symmetry). -/
def unitAffineSymmetry {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    (forget₂ _ AddCommGrpCat).obj
      ((RingedSpace.moduleCohomology (Limits.pullback g f).toRingedSpace 1).obj
        ((tensorPullback (pullback.snd g f)).obj (SheafOfModules.unit X.ringCatSheaf))) ≅
      (forget₂ _ AddCommGrpCat).obj (coherentEdgeH f
        (SheafOfModules.unit X.ringCatSheaf) g) := by
  unfold coherentEdgeH coherentEdgeCoefficient topDegreeCohomologyOnBase
  exact unitAffineCoefficientH (pullback.snd g f) 1 ≪≫
    unitAffineHIso (pullbackSymmetry g f).symm 1 ≪≫
    (unitAffineCoefficientH (pullback.fst f g) 1).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unitHMap_smul {X Y : Scheme.{u}} (h : X ⟶ Y) (q : ℕ)
    (a : Γ(Y, ⊤)) (x : unitAffineH Y q) :
    unitAffineHMap h q (a • x) = h.appTop a • unitAffineHMap h q x := by
  obtain ⟨L, hL⟩ := moduleCohomologyFMap_basic_linearity h
    (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) q
  have hs := L.hom.map_smul a x
  unfold unitAffineHMap
  rw [← hL]
  exact hs

attribute [local irreducible] unitAffineHMap unitAffineHIso unitAffineSymmetry

/-- Canonical structural-unit cohomology transport component.
Source: Stacks, Tags 01F8, 01FB, 0096 and 0097.
(blueprint: new-unit-affine-symmetry). -/
theorem unitAffineSymmetry_smul {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (a : Γ(T, ⊤))
    (x : (RingedSpace.moduleCohomology (Limits.pullback g f).toRingedSpace 1).obj
      ((tensorPullback (pullback.snd g f)).obj (SheafOfModules.unit X.ringCatSheaf))) :
    (unitAffineSymmetry f g).hom ((pullback.fst g f).appTop a • x) =
      a • (unitAffineSymmetry f g).hom x := by
  have hs := unitHMap_smul (pullbackSymmetry g f).inv 1
    ((pullback.fst g f).appTop a) ((unitAffineCoefficientH (pullback.snd g f) 1).hom x)
  have hp : (pullbackSymmetry g f).inv.appTop ((pullback.fst g f).appTop a) =
      (pullback.snd f g).appTop a := by
    change ((pullback.fst g f).appTop ≫ (pullbackSymmetry g f).inv.appTop) a = _
    rw [← Scheme.Hom.comp_appTop]
    simp
  rw [hp] at hs
  unfold unitAffineSymmetry unitAffineHIso
  change (unitAffineCoefficientH (pullback.fst f g) 1).inv
    (unitAffineHMap (pullbackSymmetry g f).inv 1
      ((unitAffineCoefficientH (pullback.snd g f) 1).hom
        ((pullback.fst g f).appTop a • x))) =
    (pullback.snd f g).appTop a •
      (unitAffineCoefficientH (pullback.fst f g) 1).inv
        (unitAffineHMap (pullbackSymmetry g f).inv 1
          ((unitAffineCoefficientH (pullback.snd g f) 1).hom x))
  rw [unitCoefficientH_hom_smul, hs, unitCoefficientH_inv_smul]

end Construction

attribute [-instance] unitAffineSectionsModule unitAffineCohomModule
  unitAffineForgetCohomModule unitAffineHModule unitAffineForgetModule
attribute [local irreducible] RingedSpace.moduleCohomology tensorPullback tensorPullbackObj
  unitAffineSymmetry unitAffineSectionsEquiv
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

/-- Compose the explicit cohomology symmetry with one affine linear comparison.
Source: Stacks, Tag 0ATM (blueprint: new-unit-affine-symmetry). -/
def unitAffineComparison {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Etale)
    (E : S.Modules)
    (e : coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) V.hom ≃ₗ[Γ(V.left, ⊤)]
      (RingedSpace.globalSectionsFunctor V.left.toRingedSpace).obj ((tensorPullback V.hom).obj E)) :
    (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace 1).obj
      (affineRealizationCoefficient f (SheafOfModules.unit X.ringCatSheaf) V) ≃+
        Γ((tensorPullback V.hom).obj E, ⊤) :=
  (unitAffineSymmetry f V.hom).addCommGroupIsoToAddEquiv.trans
    (e.toAddEquiv.trans (unitAffineSectionsEquiv V.left ((tensorPullback V.hom).obj E)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
/-- The pointwise comparison is linear for the projection action.
Source: Stacks, Tag 0ATM (blueprint: new-unit-affine-symmetry). -/
theorem unitAffineComparison_smul {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Etale)
    (E : S.Modules)
    (e : coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) V.hom ≃ₗ[Γ(V.left, ⊤)]
      (RingedSpace.globalSectionsFunctor V.left.toRingedSpace).obj ((tensorPullback V.hom).obj E))
    (a : Γ(V.left, ⊤))
    (x : (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace 1).obj
      (affineRealizationCoefficient f (SheafOfModules.unit X.ringCatSheaf) V)) :
    unitAffineComparison f V E e ((pullback.fst V.hom f).appTop a • x) =
      a • unitAffineComparison f V E e x := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types false in
  first
  | let : Module Γ(Limits.pullback V.hom f, ⊤)
        ((RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace 1).obj
          (affineRealizationCoefficient f (SheafOfModules.unit X.ringCatSheaf) V)) :=
      unitAffineCohomModule _ _ _
    let : Module Γ(V.left, ⊤)
        ((RingedSpace.globalSectionsFunctor V.left.toRingedSpace).obj
          ((tensorPullback V.hom).obj E)) := unitAffineSectionsModule _ _
    change unitAffineSectionsEquiv V.left ((tensorPullback V.hom).obj E)
      (e ((unitAffineSymmetry f V.hom).hom ((pullback.fst V.hom f).appTop a • x))) = _
    exact (congrArg (fun y ↦ unitAffineSectionsEquiv V.left ((tensorPullback V.hom).obj E) (e y))
      (unitAffineSymmetry_smul f V.hom a x)).trans
      ((congrArg (unitAffineSectionsEquiv V.left ((tensorPullback V.hom).obj E))
        (e.map_smul a ((unitAffineSymmetry f V.hom).hom x))).trans
        (unitAffineSectionsEquiv_smul V.left ((tensorPullback V.hom).obj E) a _))

attribute [irreducible] unitAffineComparison

set_option linter.unusedVariables false in
/-- The explicit comparison family, including evaluation as global sections.
Source: Stacks, Tag 0ATM (blueprint: new-unit-affine-symmetry). -/
@[irreducible] def unitAffineComparisonFamily {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (E : S.Modules) [E.IsQuasicoherent]
    (e : ∀ (T : Scheme.{u}) (g : T ⟶ S) (_ : IsAffine T),
      coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g ≃ₗ[Γ(T, ⊤)]
        (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
          ((tensorPullback g).obj E))
    (e_natural : ∀ (T T' : Scheme.{u}) (g : T ⟶ S) (h : T' ⟶ T)
      (hT : IsAffine T) (hT' : IsAffine T')
      (x : coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g),
      e T' (h ≫ g) hT' (coherentEdgePullback f
        (SheafOfModules.unit X.ringCatSheaf) g h x) =
      coherentEdgeRho g h E (e T g hT x)) :
    ∀ (V : S.Etale) [IsAffine V.left],
      (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace 1).obj
        (affineRealizationCoefficient f (SheafOfModules.unit X.ringCatSheaf) V) ≃+
          Γ((tensorPullback V.hom).obj E, ⊤) :=
  fun V _ ↦ unitAffineComparison f V E (e V.left V.hom inferInstance)


end
end AlgebraicGeometry.Scheme.Modules
