/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.Paper.ModuleCupRealizationComplexData
public import Sheaf.Paper.ModuleCupNaiveDerivedCompatibility
public import Sheaf.Paper.ModuleCupDerivedHomologyTensor
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-! # Comparing resolution classes with the homology of derived global sections

Source: Stacks Project, Tags 01DZ and 0FKU.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable (X : Scheme.{u})
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

@[instance_reducible] local instance : CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))

/-- Derived global sections of a coefficient sheaf placed in degree zero. -/
abbrev cupDerivedSections (F : X.Modules) :=
  (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)

/-- A comparison with derived global sections, including the representative formula.
The cycles in integer degrees are obtained by the actual extension by zero. -/
structure CupDerivedClassComparison where
  equiv : ∀ (F : X.Modules) (n : ℕ),
    (RingedSpace.moduleCohomology X.toRingedSpace n).obj F ≃ₗ[Γ(X, ⊤)]
      (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) (n : ℤ)).obj
        (cupDerivedSections X F)
  on_cycles : ∀ {F : X.Modules} (D : CupAcyclicResolution F) (n : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.K).sc n).moduleCatLeftHomologyData.K),
    let K := ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj D.integerComplex
    ∃ z : K.cycles (n : ℤ),
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).map
        (D.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).hom) (K.iCycles n z) =
          a.val ∧
      equiv F n (D.class n a) =
        (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) (n : ℤ)).map
          (moduleCup_globalComparison X D.integerComplex ≫
            (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map
              (inv D.derivedAugmentation))
          (cupLocalizedCycleClass K n z)

local instance : (RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive :=
  RingedSpace.globalSectionsFunctor_additive X.toRingedSpace

set_option backward.isDefEq.respectTransparency.types true in
private def injectiveData
    {F : SheafOfModules.{u} (moduleRings X.toRingedSpace)} (I : InjectiveResolution F) :
    CupAcyclicResolution F where
  K := I.cocomplex
  augmentation := I.ι
  quasiIso := inferInstance
  I := I
  comparison := 𝟙 _
  over := by simp
  computes := fun n ↦ by
    change IsIso (HomologicalComplex.homologyMap
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (.up ℕ) |>.map (𝟙 I.cocomplex)) n)
    simp only [CategoryTheory.Functor.map_id]
    infer_instance

private theorem globalComparison_isIso
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) [K.IsKInjective] :
    IsIso (moduleCup_globalComparison X K) := by
  dsimp [moduleCup_globalComparison, moduleCup_comparisonNatTrans]
  infer_instance

set_option backward.isDefEq.respectTransparency.types true in
private def sectionHomologyIso
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℕ) (n : ℕ) :
    (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) ≅
    (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (.up ℕ)).obj K).homology n :=
  (HomologicalComplex.homologyFunctor _ _ (n : ℤ)).mapIso
      (K.mapExtendIso ComplexShape.embeddingUpNat
        (RingedSpace.globalSectionsFunctor X.toRingedSpace)) ≪≫
    (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (.up ℕ)).obj K).extendHomologyIso ComplexShape.embeddingUpNat rfl

set_option backward.isDefEq.respectTransparency.types true in
private def sectionCyclesIso
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℕ) (n : ℕ) :
    (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat)).cycles (n : ℤ) ≅
    (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (.up ℕ)).obj K).cycles n :=
  (HomologicalComplex.cyclesFunctor _ _ (n : ℤ)).mapIso
      (K.mapExtendIso ComplexShape.embeddingUpNat
        (RingedSpace.globalSectionsFunctor X.toRingedSpace)) ≪≫
    (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (.up ℕ)).obj K).extendCyclesIso ComplexShape.embeddingUpNat rfl

set_option backward.isDefEq.respectTransparency.types true in
omit [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] in
private theorem sectionCyclesIso_iCycles
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℕ) (n : ℕ) :
    let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
    let L := (S.mapHomologicalComplex (.up ℕ)).obj K
    let M := (S.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat)
    (sectionCyclesIso X K n).hom ≫ L.iCycles n =
      M.iCycles (n : ℤ) ≫ S.map (K.extendXIso ComplexShape.embeddingUpNat rfl).hom := by
  dsimp only [sectionCyclesIso, Iso.trans_hom, Functor.mapIso_hom]
  dsimp only [HomologicalComplex.homologyFunctor, HomologicalComplex.cyclesFunctor]
  rw [Category.assoc, HomologicalComplex.extendCyclesIso_hom_iCycles,
    ← Category.assoc]
  erw [HomologicalComplex.cyclesMap_i, Category.assoc]
  congr 1
  simp only [HomologicalComplex.mapExtendIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f, HomologicalComplex.extendXIso,
    HomologicalComplex.extend.XIso, eqToIso.hom, eqToHom_map]
  erw [HomologicalComplex.mapExtendX_hom_eq K _
    (ComplexShape.embeddingUpNat.r_f n)]
  simp only [eqToIso.hom, eqToHom_trans]

set_option backward.isDefEq.respectTransparency.types true in
omit [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] in
private theorem sectionCyclesIso_homologyπ
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℕ) (n : ℕ) :
    let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
    let L := (S.mapHomologicalComplex (.up ℕ)).obj K
    let M := (S.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat)
    M.homologyπ (n : ℤ) ≫ (sectionHomologyIso X K n).hom =
      (sectionCyclesIso X K n).hom ≫ L.homologyπ n := by
  dsimp only [sectionHomologyIso, sectionCyclesIso, Iso.trans_hom, Functor.mapIso_hom]
  dsimp only [HomologicalComplex.homologyFunctor, HomologicalComplex.cyclesFunctor]
  rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc,
    HomologicalComplex.homologyπ_extendHomologyIso_hom, Category.assoc]

set_option backward.isDefEq.respectTransparency.types true in
omit [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] in
private theorem sectionHomologyIso_naturality
    {K L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℕ}
    (f : K ⟶ L) (n : ℕ) :
    let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
    HomologicalComplex.homologyMap ((S.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)) (n : ℤ) ≫
      (sectionHomologyIso X L n).hom =
    (sectionHomologyIso X K n).hom ≫
      HomologicalComplex.homologyMap ((S.mapHomologicalComplex (.up ℕ)).map f) n := by
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  have h : (S.mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat) ≫
        (L.mapExtendIso ComplexShape.embeddingUpNat S).hom =
      (K.mapExtendIso ComplexShape.embeddingUpNat S).hom ≫
        HomologicalComplex.extendMap ((S.mapHomologicalComplex (.up ℕ)).map f)
          ComplexShape.embeddingUpNat := by
    ext i : 1
    exact HomologicalComplex.mapExtensIso_hom_f_naturality
      f ComplexShape.embeddingUpNat S i
  dsimp only [sectionHomologyIso, Iso.trans_hom, Functor.mapIso_hom]
  dsimp only [HomologicalComplex.homologyFunctor, HomologicalComplex.cyclesFunctor]
  rw [← HomologicalComplex.homologyMap_comp_assoc, h,
    HomologicalComplex.homologyMap_comp_assoc,
    HomologicalComplex.extendHomologyIso_hom_naturality, Category.assoc]

private theorem augmentation_comparison
    {F : SheafOfModules.{u} (moduleRings X.toRingedSpace)} (D : CupAcyclicResolution F)
    (J : InjectiveResolution F) :
    D.derivedAugmentation ≫ DerivedCategory.Q.map
        (HomologicalComplex.extendMap
          (D.comparison ≫ (InjectiveResolution.homotopyEquiv D.I J).hom)
          ComplexShape.embeddingUpNat) =
      (injectiveData X J).derivedAugmentation := by
  unfold CupAcyclicResolution.derivedAugmentation
  rw [← Functor.map_comp, Category.assoc,
    ← HomologicalComplex.extendMap_comp, ← Category.assoc, D.over,
    InjectiveResolution.homotopyEquiv_hom_ι]
  rfl

set_option backward.isDefEq.respectTransparency.types true in
private theorem global_transport
    {F : SheafOfModules.{u} (moduleRings X.toRingedSpace)} (D : CupAcyclicResolution F)
    (J : InjectiveResolution F) :
    let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
    let f := HomologicalComplex.extendMap
      (D.comparison ≫ (InjectiveResolution.homotopyEquiv D.I J).hom)
      ComplexShape.embeddingUpNat
    moduleCup_globalComparison X D.integerComplex ≫
        S.rightDerivedFunctor.map (inv D.derivedAugmentation) =
      DerivedCategory.Q.map ((S.mapHomologicalComplex (.up ℤ)).map f) ≫
        moduleCup_globalComparison X (injectiveData X J).integerComplex ≫
          S.rightDerivedFunctor.map (inv (injectiveData X J).derivedAugmentation) := by
  dsimp only
  rw [← Category.assoc]
  erw [(moduleCup_comparisonNatTrans X).naturality]
  dsimp only [Functor.comp_map]
  rw [Category.assoc, ← Functor.map_comp]
  congr 2
  apply (cancel_mono (injectiveData X J).derivedAugmentation).mp
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
    ← augmentation_comparison X D J, IsIso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency.types true in
private def injectiveClassIso
    {F : SheafOfModules.{u} (moduleRings X.toRingedSpace)}
    (I : InjectiveResolution F) (n : ℕ) :
    (RingedSpace.moduleCohomology X.toRingedSpace n).obj F ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) (n : ℤ)).obj
        (cupDerivedSections X F) := by
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let D := injectiveData X I
  have : D.integerComplex.IsKInjective := by
    change CochainComplex.IsKInjective (I.cocomplex.extend ComplexShape.embeddingUpNat)
    exact CochainComplex.isKInjective_of_injective _ 0
  have := globalComparison_isIso X D.integerComplex
  exact I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n ≪≫
    (sectionHomologyIso X I.cocomplex n).symm ≪≫
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} Γ(X, ⊤)) (n : ℤ)).app
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (.up ℤ)).obj D.integerComplex)).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) (n : ℤ)).mapIso
      (asIso (moduleCup_globalComparison X D.integerComplex ≫
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map
          (inv D.derivedAugmentation)))

attribute [local irreducible] Functor.rightDerivedFunctor
  moduleCup_globalComparison moduleCup_comparisonNatTrans

set_option maxHeartbeats 1000000 in
-- The two category presentations of module sheaves require extra definitional equality work.
set_option backward.isDefEq.respectTransparency.types true in
private theorem injectiveClassIso_transport
    {F : SheafOfModules.{u} (moduleRings X.toRingedSpace)}
    (D : CupAcyclicResolution F) (J : InjectiveResolution F) (n : ℕ) :
    let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
    let K := (S.mapHomologicalComplex (.up ℤ)).obj D.integerComplex
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) (n : ℤ)
    letI : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
      (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
    letI : EnoughInjectives X.Modules :=
      (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
    letI : S.Additive := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
    (sectionHomologyIso X D.K n).hom ≫
        HomologicalComplex.homologyMap ((S.mapHomologicalComplex (.up ℕ)).map D.comparison) n ≫
        (D.I.isoRightDerivedObj S n).inv ≫ (injectiveClassIso X J n).hom =
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} Γ(X, ⊤)) (n : ℤ)).app K).inv ≫
        H.map (moduleCup_globalComparison X D.integerComplex ≫
          S.rightDerivedFunctor.map (inv D.derivedAugmentation)) := by
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let : S.Additive := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) (n : ℤ)
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let φ := (InjectiveResolution.homotopyEquiv D.I J).hom
  have hn : (D.I.isoRightDerivedObj S n).inv ≫ (J.isoRightDerivedObj S n).hom =
      HomologicalComplex.homologyMap ((S.mapHomologicalComplex (.up ℕ)).map φ) n := by
    have h := InjectiveResolution.isoRightDerivedObj_hom_naturality
      (𝟙 F) D.I J φ (by
        have h := congrArg (fun f ↦ f.f 0)
          (InjectiveResolution.homotopyEquiv_hom_ι D.I J)
        simpa only [HomologicalComplex.comp_f, Category.id_comp] using h) S n
    dsimp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] at h
    erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
    simpa only [Category.assoc, Iso.inv_hom_id_assoc,
      HomologicalComplex.homologyFunctor_map] using
      congrArg (fun f ↦ (D.I.isoRightDerivedObj S n).inv ≫ f) h
  simp only [injectiveClassIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    asIso_hom]
  rw [← Category.assoc (D.I.isoRightDerivedObj S n).inv, hn,
    ← HomologicalComplex.homologyMap_comp_assoc, ← Functor.map_comp]
  erw [← Category.assoc (sectionHomologyIso X D.K n).hom,
    ← sectionHomologyIso_naturality X (D.comparison ≫ φ) n]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [global_transport X D J, Functor.map_comp]
  have h := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} Γ(X, ⊤))
    (n : ℤ)).inv.naturality
      ((S.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap (D.comparison ≫ φ) ComplexShape.embeddingUpNat))
  dsimp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] at h
  simpa only [Category.assoc, Functor.map_comp,
    HomologicalComplex.homologyFunctor_map, H, S, φ,
    CupAcyclicResolution.integerComplex, injectiveData, cupDerivedSections,
    HomologicalComplex.homologyFunctor_obj, DerivedCategory.Q_obj_single_obj,
    Iso.app_inv] using congrArg
    (fun f ↦ f ≫ H.map (moduleCup_globalComparison X (injectiveData X J).integerComplex ≫
      S.rightDerivedFunctor.map (inv (injectiveData X J).derivedAugmentation))) h

/-- The right-derived cohomology functor agrees with homology of RΓ, with its
canonical formula on every computing resolution.
Source: Stacks Project, Tag 01DZ, computation by injective resolutions;
Tag 0FKU, global specialization of the comparison diagram.
(blueprint: lem-sc-module-cup-derived-class-comparison)
Proof: choose an injective resolution of F and extend it by zero to integers.
This bounded-below complex of injectives is K-injective, so the right-derived
comparison unit at it is invertible. The localized augmentation is invertible
as well. The homology factorization of localization and the extension homology
isomorphism therefore identify H^n(RΓ(F[0])) with H^n(Γ(I)). Compose with the
inverse of I.isoRightDerivedObj to obtain equiv, in the displayed direction.
For another computing resolution D, extend D.comparison by zero. Its equation
over the augmentation and naturality of the derived comparison identify the
localized composite with the chosen comparison above. The map on global
homology is precisely the one in D.class; computes says it is invertible.
The extension cycles isomorphism lifts a to z and identifies its component
through extendXIso. Naturality of homologyπ then gives the displayed equation.
Independence of the injective resolution follows from comparison maps over F
and their homotopies. At n=0 extension has a zero incoming differential, just
as the natural complex does; zero sheaves and zero cycles cause no exception. -/
theorem exists_cupDerivedClassComparison : Nonempty (CupDerivedClassComparison X) := by
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  refine ⟨{
    equiv := fun F n ↦ (injectiveClassIso X (injectiveResolution F) n).toLinearEquiv
    on_cycles := ?_ }⟩
  intro F D n a
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let L := (S.mapHomologicalComplex (.up ℕ)).obj D.K
  let K := (S.mapHomologicalComplex (.up ℤ)).obj D.integerComplex
  let c : L.cycles n := (L.sc n).moduleCatCyclesIso.inv a
  let z : K.cycles (n : ℤ) := (sectionCyclesIso X D.K n).inv c
  refine ⟨z, ?_, ?_⟩
  · have h := congrArg (fun f ↦ f z) (sectionCyclesIso_iCycles X D.K n)
    have hc := congrArg (fun f ↦ f a) (L.sc n).moduleCatCyclesIso_inv_iCycles
    simp only [ModuleCat.comp_apply] at h hc
    have hz : (sectionCyclesIso X D.K n).hom z = c := by
      exact (sectionCyclesIso X D.K n).inv_hom_id_apply c
    rw [hz] at h
    change L.iCycles n c = a.val at hc
    exact h.symm.trans hc
  · have h := congrArg (fun f ↦ f z) (sectionCyclesIso_homologyπ X D.K n)
    have ht := congrArg (fun f ↦ f (K.homologyπ (n : ℤ) z))
      (injectiveClassIso_transport X D (injectiveResolution F) n)
    dsimp only [CupAcyclicResolution.class, cupCycleClass, cupLocalizedCycleClass,
      CategoryTheory.Iso.toLinearEquiv_apply] at *
    simp only [ModuleCat.comp_apply] at h ht
    have hz : (sectionCyclesIso X D.K n).hom z = c :=
      (sectionCyclesIso X D.K n).inv_hom_id_apply c
    rw [hz] at h
    rw [h] at ht
    exact ht

end
end AlgebraicGeometry.Scheme.Modules
