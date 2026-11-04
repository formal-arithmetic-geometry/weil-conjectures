/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerDirectImageSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalAdjunctionUnit

/-! # Actual completed pullback versus the canonical pro-étale ring pullback

The actual completed module pullback `pbcActualModulePull g d` and the canonical pro-étale
ring pullback along the invertible completed coefficient map agree, by the object equality
of the scalar-extension interface. Their derived functors are left adjoints of the same
derived direct image, and the comparison is compatible with both derived adjunctions.

Source: Stacks Tags 03D2, 099N and 0D6D
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

/-- The completed coefficient map is invertible.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
theorem pbcCompletedCoefficientMap_isIso : IsIso (completedCoefficientMap g d) :=
  completedCoefficient_isIso g d

/-- The completed coefficient map, as an isomorphism of ring sheaves.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
abbrev pbcActualCoefficientIso :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (pbcAdicCompletion Y d) ≅
      pbcAdicCompletion X d :=
  letI := pbcCompletedCoefficientMap_isIso g d
  asIso (completedCoefficientMap g d)

@[simp]
theorem pbcActualCoefficientIso_hom :
    (pbcActualCoefficientIso g d).hom = completedCoefficientMap g d := rfl

/-- The actual derived direct image is the canonical pro-étale derived direct image.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
theorem pbcActualDerivedPush_eq :
    pbcActualDerivedPush g d = proEtaleRingDerivedDirectImage g (pbcAdicCompletion Y d)
      (pbcAdicCompletion X d) (pbcActualCoefficientIso g d) := rfl

/-- The object equality of the scalar-extension interface gives the identity on sheafified
tensors. Source: Stacks Tag 03EK
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
def pbcActualModulePullIsoApp (M : pbcModules Y (pbcAdicCompletion Y d)) :
    (pbcActualModulePull g d).obj M ≅
      (proEtaleRingModulePullback g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
        (pbcActualCoefficientIso g d)).obj M :=
  eqToIso ((completedAdicChangeData X (completedCoefficientMap g d)).choose_spec.choose
    ((proEtaleModuleInverseImage g (pbcAdicCompletion Y d)).obj M))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The object equality in the scalar-extension interface is natural.
Source: Stacks Tag 03EK (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: both maps are sheafifications of r ⊗ x ↦ r ⊗ a(x), by the morphism
characterization in completedAdicChangeData. -/
theorem pbcActualModulePullIso_naturality
    (M N : pbcModules Y (pbcAdicCompletion Y d)) (a : M ⟶ N) :
    (pbcActualModulePull g d).map a ≫ (pbcActualModulePullIsoApp g d N).hom =
      (pbcActualModulePullIsoApp g d M).hom ≫
        (proEtaleRingModulePullback g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
          (pbcActualCoefficientIso g d)).map a := by
  let h := (completedAdicChangeData X (completedCoefficientMap g d)).choose_spec.choose
  change (completedAdicChangeData X (completedCoefficientMap g d)).choose.map
      ((proEtaleModuleInverseImage g _).map a) ≫ eqToHom (h _) =
    eqToHom (h _) ≫ SheafOfModules.changeOfRingsHom
      (completedCoefficientMap g d) _ ((proEtaleModuleInverseImage g _).map a)
  erw [(completedAdicChangeData X (completedCoefficientMap g d)).choose_spec.choose_spec.choose
      ((proEtaleModuleInverseImage g _).map a)]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The object equality of the scalar-extension interface, as a natural isomorphism of
module pullbacks. Source: Stacks Tag 03EK
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
def pbcActualModulePullIso :
    pbcActualModulePull g d ≅ proEtaleRingModulePullback g (pbcAdicCompletion Y d)
      (pbcAdicCompletion X d) (pbcActualCoefficientIso g d) :=
  NatIso.ofComponents (fun M ↦ pbcActualModulePullIsoApp g d M)
    (fun {M N} a ↦ pbcActualModulePullIso_naturality g d M N a)

/-- The module comparison induced on homotopy categories.
Source: Stacks Tag 03EK (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
def pbcActualModulePullHomotopyIso :
    (pbcActualModulePull g d).mapHomotopyCategory (.up ℤ) ≅
      (proEtaleRingModulePullback g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
        (pbcActualCoefficientIso g d)).mapHomotopyCategory (.up ℤ) where
  hom := NatTrans.mapHomotopyCategory (pbcActualModulePullIso g d).hom (.up ℤ)
  inv := NatTrans.mapHomotopyCategory (pbcActualModulePullIso g d).inv (.up ℤ)
  hom_inv_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id, NatTrans.mapHomotopyCategory_id]
  inv_hom_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id, NatTrans.mapHomotopyCategory_id]

/-- The derived comparison between the actual derived pullback and the canonical one,
retaining the universal counit on every complex.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
def pbcActualPullProEtaleIso :
    pbcActualDerivedPull g d ≅ proEtaleRingDerivedPullback g (pbcAdicCompletion Y d)
      (pbcAdicCompletion X d) (pbcActualCoefficientIso g d) :=
  Functor.leftDerivedNatIso _ _ (pbcActualPullCounit g d)
    (proEtaleRingModulePullback g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (pbcActualCoefficientIso g d)).mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))
    (Functor.isoWhiskerRight (pbcActualModulePullHomotopyIso g d) DerivedCategory.Qh)

/-- The derived comparison is the homotopy-category module comparison after the two
universal counits.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
@[reassoc]
theorem pbcActualPullProEtaleIso_hom_app_counit
    (K : HomotopyCategory (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) :
    (pbcActualPullProEtaleIso g d).hom.app (DerivedCategory.Qh.obj K) ≫
        (proEtaleRingModulePullback g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
          (pbcActualCoefficientIso g d)).mapDerivedCategoryFactorsh.hom.app K =
      (pbcActualPullCounit g d).app K ≫
        DerivedCategory.Qh.map ((pbcActualModulePullHomotopyIso g d).hom.app K) :=
  Functor.leftDerivedNatTrans_app _ _ _ _
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) _ K

/-- The inverse derived comparison, after the universal counits.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
@[reassoc]
theorem pbcActualPullProEtaleIso_inv_app_counit
    (K : HomotopyCategory (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) :
    (pbcActualPullProEtaleIso g d).inv.app (DerivedCategory.Qh.obj K) ≫
        (pbcActualPullCounit g d).app K =
      (proEtaleRingModulePullback g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
          (pbcActualCoefficientIso g d)).mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((pbcActualModulePullHomotopyIso g d).inv.app K) :=
  Functor.leftDerivedNatTrans_app _ _ _ _
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) _ K

/-- The derived comparison is the ordinary module comparison on every complex.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
theorem pbcActualPullProEtaleIso_fac
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :
    (pbcActualPullProEtaleIso g d).hom.app (DerivedCategory.Q.obj P) ≫
        (proEtaleRingDerivedPullbackFactors g (pbcAdicCompletion Y d)
          (pbcAdicCompletion X d) (pbcActualCoefficientIso g d)).hom.app P =
      pbcActualPullComplexCounit g d P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (pbcActualModulePullIso g d) (.up ℤ)).hom.app P) := by
  let G := proEtaleRingModulePullback g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
    (pbcActualCoefficientIso g d)
  have h := G.mapDerivedCategoryFactorsh_hom_app P
  have h' : G.mapDerivedCategoryFactors.hom.app P =
      G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj P) ≫
        DerivedCategory.Qh.map ((G.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj P) := by
    rw [h]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      Quotient.lift.isLift_hom, Quotient.lift.isLift_inv, CategoryTheory.Functor.map_id]
    erw [Category.id_comp, Category.comp_id]
  have hh : (pbcActualModulePullHomotopyIso g d).hom.app ((HomotopyCategory.quotient _ _).obj P) ≫
      (G.mapHomotopyCategoryFactors (.up ℤ)).hom.app P =
      ((pbcActualModulePull g d).mapHomotopyCategoryFactors (.up ℤ)).hom.app P ≫
        (HomotopyCategory.quotient _ _).map
          ((NatIso.mapHomologicalComplex (pbcActualModulePullIso g d) (.up ℤ)).hom.app P) := by
    simp [pbcActualModulePullHomotopyIso, Functor.mapHomotopyCategoryFactors]
    rfl
  rw [proEtaleRingDerivedPullbackFactors, h', ← NatTrans.naturality_assoc]
  erw [pbcActualPullProEtaleIso_hom_app_counit_assoc]
  rw [pbcActualPullComplexCounit]
  simp only [Category.assoc]
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, hh]

/-- The canonical module unit, followed by the module comparison, is the actual module unit.
Source: Stacks Tags 03D2 and 03EK
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: both units send a section to the sheafified tensor `1 ⊗ x` of its model-site
inverse-image unit; the comparison is the object equality of the scalar-extension data. -/
theorem pbcActualModuleAdjunction_unit_app (M : pbcModules Y (pbcAdicCompletion Y d)) :
    (proEtaleRingModuleAdjunction g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
        (pbcActualCoefficientIso g d)).unit.app M ≫
      (pbcActualModulePush g d).map ((pbcActualModulePullIso g d).inv.app M) =
    (pbcActualModuleAdjunction g d).unit.app M := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  rintro ⟨U⟩
  ext x
  have h₁ : ((pbcActualModuleAdjunction g d).unit.app M).val.app (op U) x =
      pbcActualModuleUnitSection g d M U x :=
    (pbcActualModuleAdjunction_exists g d).exists.choose_spec M U x
  have h₂ := proEtaleRingModuleAdjunction_normalized g (pbcAdicCompletion Y d)
    (pbcAdicCompletion X d) (pbcActualCoefficientIso g d) M U x
  refine Eq.trans ?_ h₁.symm
  refine (congrArg (fun y ↦ (((pbcActualModulePush g d).map
    ((pbcActualModulePullIso g d).inv.app M)).val.app (op U)) y) h₂).trans ?_
  rfl

/-- The actual derived unit is the canonical derived unit followed by the comparison.
Source: Stacks Tags 03D2 and 099N
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: both sides are maps into the left derived functor of the composite, so it suffices
to compare them after the universal counit on homotopy representatives. There they are the
two ordinary units, which agree after the module comparison. -/
theorem pbcActualDerivedAdjunction_unit :
    (pbcActualDerivedAdjunction g d).unit =
      (proEtaleRingDerivedAdjunction g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
          (pbcActualCoefficientIso g d)).unit ≫
        Functor.whiskerRight (pbcActualPullProEtaleIso g d).inv (pbcActualDerivedPush g d) := by
  let adj₁ := pbcActualModuleAdjunction g d
  let adj₂ := proEtaleRingModuleAdjunction g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
    (pbcActualCoefficientIso g d)
  have hu (K : HomotopyCategory (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) :=
    Adjunction.mapHomotopyCategory_unit_app_comp (.up ℤ) adj₂ adj₁
      (pbcActualModulePullIso g d).inv (𝟙 _)
      (fun M ↦ (pbcActualModuleAdjunction_unit_app g d M).trans (Category.comp_id _).symm) K
  apply Functor.leftDerived_ext (pbcActualDerivedPull g d ⋙ pbcActualDerivedPush g d)
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (pbcActualPullCounit g d) (pbcActualDerivedPush g d))
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc, ← Functor.map_comp]
  rw [pbcActualPullProEtaleIso_inv_app_counit, pbcActualDerivedAdjunction, Adjunction.derived_unit,
    Adjunction.derivedη_fac_app, CategoryTheory.Functor.map_comp, ← Category.assoc]
  erw [proEtaleRingDerivedAdjunction, Adjunction.mapDerivedCategoryRightDerivedAdjunction,
    Adjunction.derived_unit, Adjunction.derivedη_fac_app]
  rw [Category.assoc]
  erw [← (pbcActualPushUnit g d).naturality]
  rw [Functor.comp_map, ← Functor.map_comp_assoc]
  erw [hu K]
  rw [NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
  erw [Category.comp_id]

/-- The comparison intertwines the actual derived adjunction with the canonical one.
Source: Stacks Tags 03D2 and 099N
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
theorem pbcActualDerivedAdjunction_homEquiv
    (M : PbcCompletedDerived Y d) (N : PbcCompletedDerived X d)
    (t : (pbcActualDerivedPull g d).obj M ⟶ N) :
    (pbcActualDerivedAdjunction g d).homEquiv M N t =
      (proEtaleRingDerivedAdjunction g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
        (pbcActualCoefficientIso g d)).homEquiv M N
          ((pbcActualPullProEtaleIso g d).inv.app M ≫ t) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, pbcActualDerivedAdjunction_unit,
    NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc, ← CategoryTheory.Functor.map_comp]
  rfl

end AlgebraicGeometry.Scheme
