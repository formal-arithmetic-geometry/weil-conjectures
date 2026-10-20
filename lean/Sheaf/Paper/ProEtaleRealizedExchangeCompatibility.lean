/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.Paper.RingedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# Realized pro-etale operations and exchange compatibility

Source: Stacks Project, Tags 00YV, 03D2, 07A7, 0D6D and 0D6E.
The coefficient identifications are conjugates of the canonical constant comparison.
No properness or etale-origin condition is involved in this normalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The fixed-scalar realization is an equivalence, with its recorded functor.
Source: Stacks Tag 00YV (blueprint: def-weil-pbc-etale-origin-witness). -/
instance etaleOriginRealization_isEquivalence (T : Scheme.{u}) :
    (etaleOriginRealization T Λ).IsEquivalence :=
  (etaleOriginRealization_properties T Λ).2.2.2

/-- The canonical coefficient identification conjugated by specified presentations.
Source: Stacks Tags 098T and 00YV
(blueprint: lem-weil-pbc-realized-exchange-compatibility). -/
def proEtaleRealizedCoefficientIso {U V : Scheme.{u}} (h : U ⟶ V)
    {R_V : Sheaf (ProEt.topology V) CommRingCat.{u + 1}}
    {R_U : Sheaf (ProEt.topology U) CommRingCat.{u + 1}}
    (eV : etaleOriginRing V Λ ≅ R_V) (eU : etaleOriginRing U Λ ≅ R_U) :
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R_V ≅ R_U :=
  (proEtaleSheafInverseImage h CommRingCat.{u + 1}).mapIso eV.symm ≪≫
    (letI : ∀ n : ℕᵒᵖ,
        Finite (((Functor.const ℕᵒᵖ).obj (CommRingCat.of Λ)).obj n) :=
      fun _ ↦ inferInstanceAs (Finite Λ)
    @asIso _ _ _ _ ((proEtaleConstantComparison h).app (CommRingCat.of Λ))
      ((proEtale_profinite_coefficient_inverse_image
        ((Functor.const ℕᵒᵖ).obj (CommRingCat.of Λ))).1 U V h (Opposite.op 0))) ≪≫ eU

/-- The conjugated constant coefficient identifications commute with composition.
Source: the finite-level coherence of profinite coefficient inverse image. -/
theorem proEtaleRealizedCoefficientIso_comp {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (eV : etaleOriginRing V Λ ≅ RV) (eW : etaleOriginRing W Λ ≅ RW)
    (eZ : etaleOriginRing Z Λ ≅ RZ) :
    proEtaleRingCompositeCoefficients h k RV RW RZ
        (proEtaleRealizedCoefficientIso Λ k eV eW)
        (proEtaleRealizedCoefficientIso Λ h eW eZ) =
      proEtaleRealizedCoefficientIso Λ (h ≫ k) eV eZ := by
  let Q := (Functor.const ℕᵒᵖ).obj (CommRingCat.of Λ)
  let : ∀ n : ℕᵒᵖ, Finite (Q.obj n) := fun _ ↦ inferInstanceAs (Finite Λ)
  have hc := (proEtale_profinite_coefficient_inverse_image Q).2.2.2.2.2.2.2.2.2.1
    Z W V h k (Opposite.op 0)
  dsimp [Q, proEtaleCoefficientTower] at hc
  apply Iso.ext
  dsimp [proEtaleRingCompositeCoefficients, proEtaleRealizedCoefficientIso]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (proEtaleSheafInverseImage h CommRingCat.{u + 1})
    eW.hom eW.inv]
  simp only [Iso.hom_inv_id]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := (proEtaleRingInverseImageComp h k).hom.naturality eV.inv
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [hc]
  simp only [Category.assoc]

/-- Restrict a module sheaf to its constant scalar action. -/
def proEtaleConstantSections (T : Scheme.{u}) :
    proEtaleRingModules T (etaleOriginRing T Λ) ⥤
      Sheaf (ProEt.topology T) (ModuleCat.{u + 1} Λ) where
  obj M := by
    let P := (PresheafOfModules.restrictScalars (etaleOriginScalars T Λ)).obj M.val
    let F : T.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
      { obj := P.obj
        map f := P.map f
        map_id U := by ext m; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) m
        map_comp f g := by ext m; exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) m }
    exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp (ProEt.topology T) F
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) M.isSheaf⟩
  map f := ⟨
    { app U := (PresheafOfModules.restrictScalars (etaleOriginScalars T Λ)).map f.val |>.app U
      naturality := by
        intro U V i
        ext m
        exact PresheafOfModules.naturality_apply f.val i m }⟩
  map_id M := by ext U m; rfl
  map_comp f g := by ext U m; rfl

/-- The associated-module sheafification unit, in fixed-scalar coordinates. -/
def proEtaleConstantSectionsUnit (T : Scheme.{u}) :
    𝟭 (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} Λ)) ⟶
      etaleOriginRealization T Λ ⋙ proEtaleConstantSections Λ T where
  app M := ⟨
    { app U :=
        ((PresheafOfModules.sheafificationAdjunction.{u + 1} (etaleOriginScalars T Λ)).unit.app
          ((ProEtale.finiteCoefficientModulePresheaf T.ProEt Λ).obj M.obj)).app U
      naturality := by
        intro U V i
        ext m
        exact PresheafOfModules.naturality_apply
          ((PresheafOfModules.sheafificationAdjunction.{u + 1} (etaleOriginScalars T Λ)).unit.app
            ((ProEtale.finiteCoefficientModulePresheaf T.ProEt Λ).obj M.obj)) i m }⟩
  naturality := by
    intro M N f
    ext U m
    exact congrArg (fun a ↦ a.app U m)
      ((PresheafOfModules.sheafificationAdjunction.{u + 1} (etaleOriginScalars T Λ)).unit.naturality
        ((ProEtale.finiteCoefficientModulePresheaf T.ProEt Λ).map f.hom))

omit [Finite Λ] in
/-- The unit is invertible because the input is already a sheaf. -/
theorem proEtaleConstantSectionsUnit_isIso (T : Scheme.{u}) :
    IsIso (proEtaleConstantSectionsUnit Λ T) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have h : IsIso ((PresheafOfModules.sheafificationAdjunction.{u + 1}
      (etaleOriginScalars T Λ)).unit.app
        ((ProEtale.finiteCoefficientModulePresheaf T.ProEt Λ).obj M.obj)) := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj M).property
  have h' : IsIso (((sheafCompose (ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))).map
        ((proEtaleConstantSectionsUnit Λ T).app M)) := by
    rw [← isIso_iff_of_reflects_iso _
      (sheafToPresheaf (ProEt.topology T) AddCommGrpCat.{u + 1})]
    change IsIso ((PresheafOfModules.toPresheaf _).map
      ((PresheafOfModules.sheafificationAdjunction.{u + 1}
        (etaleOriginScalars T Λ)).unit.app
          ((ProEtale.finiteCoefficientModulePresheaf T.ProEt Λ).obj M.obj)))
    infer_instance
  exact isIso_of_reflects_iso _
    (sheafCompose (ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))

/-- Constant scalar restriction is the inverse of the specified realization. -/
def proEtaleConstantSectionsIsoInverse (T : Scheme.{u}) :
    proEtaleConstantSections Λ T ≅ (etaleOriginRealization T Λ).asEquivalence.inverse := by
  let E := (etaleOriginRealization T Λ).asEquivalence
  letI := proEtaleConstantSectionsUnit_isIso Λ T
  exact (Functor.leftUnitor _).symm ≪≫
    isoWhiskerRight E.counitIso.symm (proEtaleConstantSections Λ T) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft E.inverse (asIso (proEtaleConstantSectionsUnit Λ T)).symm ≪≫
    Functor.rightUnitor _

instance proEtaleConstantSections_additive (T : Scheme.{u}) :
    (proEtaleConstantSections Λ T).Additive where
  map_add := by intro M N f g; ext U m; rfl

instance proEtaleConstantSections_isEquivalence (T : Scheme.{u}) :
    (proEtaleConstantSections Λ T).IsEquivalence :=
  Functor.isEquivalence_of_iso (proEtaleConstantSectionsIsoInverse Λ T).symm

/-- The structural ring map is the canonical map on constant ring sheaves. -/
theorem proEtaleConstantCoefficient_directImageMap {U V : Scheme.{u}} (h : U ⟶ V) :
    proEtaleRingDirectImageMap h (etaleOriginRing V Λ) (etaleOriginRing U Λ)
        (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _)) =
      proEtaleConstantDirectImageMap h CommRingCat.{u + 1} (CommRingCat.of Λ) := by
  let adj := proEtaleSheafAdjunction h CommRingCat.{u + 1}
  have hc : (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _)).hom =
      proEtaleConstantInverseImageMap h CommRingCat.{u + 1} (CommRingCat.of Λ) := by
    change (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map (𝟙 _) ≫
      (proEtaleConstantComparison h).app (CommRingCat.of Λ) ≫ 𝟙 _ = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    rfl
  rw [proEtaleRingDirectImageMap, hc]
  change adj.homEquiv _ _ ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
    (proEtaleConstantDirectImageMap h CommRingCat.{u + 1} (CommRingCat.of Λ)) ≫
      adj.counit.app _) = _
  exact (adj.homEquiv _ _).apply_symm_apply _

/-- The structural ring map carries each constant scalar to the same scalar. -/
theorem proEtaleConstantCoefficient_scalar {U V : Scheme.{u}} (h : U ⟶ V)
    (W : V.ProEtᵒᵖ) :
    ((proEtaleRingDirectImageMap h (etaleOriginRing V Λ) (etaleOriginRing U Λ)
        (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _))).hom.app W).hom.comp
        ((etaleOriginScalars V Λ).app W).hom =
      ((etaleOriginScalars U Λ).app ((proEtaleBaseChange h).op.obj W)).hom := by
  rw [proEtaleConstantCoefficient_directImageMap]
  have he : toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of Λ)) ≫
        (proEtaleConstantDirectImageMap h CommRingCat.{u + 1} (CommRingCat.of Λ)).hom =
      Functor.whiskerLeft (proEtaleBaseChange h).op
        (toSheafify (ProEt.topology U) ((Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of Λ))) := by
    exact ((sheafificationAdjunction (ProEt.topology V) CommRingCat.{u + 1}).homEquiv
      ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of Λ))
      ((proEtaleSheafDirectImage h CommRingCat.{u + 1}).obj (etaleOriginRing U Λ)))
        |>.apply_symm_apply _
  exact congrArg (fun a ↦ (a.app W).hom) he

/-- The identity-on-sections direct-image comparison. -/
def proEtaleConstantSectionsDirectImage {U V : Scheme.{u}} (h : U ⟶ V) :
    proEtaleRingModuleDirectImage h (etaleOriginRing V Λ) (etaleOriginRing U Λ)
        (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _)) ⋙
      proEtaleConstantSections Λ V ⟶
    proEtaleConstantSections Λ U ⋙ ProEtale.lowerStar (ModuleCat.{u + 1} Λ) h where
  app M := ⟨
    { app W := by
        let A := ((proEtaleConstantSections Λ V).obj
          ((proEtaleRingModuleDirectImage h (etaleOriginRing V Λ) (etaleOriginRing U Λ)
            (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _))).obj M)).obj.obj W
        let B := ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) h).obj
          ((proEtaleConstantSections Λ U).obj M)).obj.obj W
        refine ModuleCat.ofHom (X := A) (Y := B) ?_
        refine { toFun := fun m ↦ m, map_add' := fun _ _ ↦ rfl, map_smul' := ?_ }
        intro r m
        let m' : M.val.obj ((proEtaleBaseChange h).op.obj W) := m
        change ((proEtaleRingDirectImageMap h (etaleOriginRing V Λ)
          (etaleOriginRing U Λ)
          (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _))).hom.app W)
            ((etaleOriginScalars V Λ).app W r) • m' =
          ((etaleOriginScalars U Λ).app ((proEtaleBaseChange h).op.obj W) r) • m'
        exact congrArg (fun a : Λ →+* (etaleOriginRing U Λ).obj.obj
          ((proEtaleBaseChange h).op.obj W) ↦ a r • m')
            (proEtaleConstantCoefficient_scalar Λ h W)
      naturality := by intro W W' i; ext m; rfl }⟩
  naturality := by intro M N f; ext W m; rfl

/-- The inverse identity-on-sections comparison. -/
def proEtaleConstantSectionsDirectImageInv {U V : Scheme.{u}} (h : U ⟶ V) :
    proEtaleConstantSections Λ U ⋙ ProEtale.lowerStar (ModuleCat.{u + 1} Λ) h ⟶
    proEtaleRingModuleDirectImage h (etaleOriginRing V Λ) (etaleOriginRing U Λ)
        (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _)) ⋙
      proEtaleConstantSections Λ V where
  app M := ⟨
    { app W := by
        let A := ((proEtaleConstantSections Λ V).obj
          ((proEtaleRingModuleDirectImage h (etaleOriginRing V Λ) (etaleOriginRing U Λ)
            (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _))).obj M)).obj.obj W
        let B := ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) h).obj
          ((proEtaleConstantSections Λ U).obj M)).obj.obj W
        refine ModuleCat.ofHom (X := B) (Y := A) ?_
        refine { toFun := fun m ↦ m, map_add' := fun _ _ ↦ rfl, map_smul' := ?_ }
        intro r m
        let m' : M.val.obj ((proEtaleBaseChange h).op.obj W) := m
        exact (congrArg (fun a : Λ →+* (etaleOriginRing U Λ).obj.obj
          ((proEtaleBaseChange h).op.obj W) ↦ a r • m')
            (proEtaleConstantCoefficient_scalar Λ h W)).symm
      naturality := by intro W W' i; ext m; rfl }⟩
  naturality := by intro M N f; ext W m; rfl

/-- The sectionwise comparison is an isomorphism of fixed-scalar sheaves. -/
def proEtaleConstantSectionsDirectImageIso {U V : Scheme.{u}} (h : U ⟶ V) :
    proEtaleRingModuleDirectImage h (etaleOriginRing V Λ) (etaleOriginRing U Λ)
        (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _)) ⋙
      proEtaleConstantSections Λ V ≅
    proEtaleConstantSections Λ U ⋙ ProEtale.lowerStar (ModuleCat.{u + 1} Λ) h where
  hom := proEtaleConstantSectionsDirectImage Λ h
  inv := proEtaleConstantSectionsDirectImageInv Λ h
  hom_inv_id := by ext M W m; rfl
  inv_hom_id := by ext M W m; rfl

/-- Constant scalar restriction respects every direct-image composition comparison
with the prescribed fibre-product-pasting section formula. -/
theorem proEtaleConstantSectionsDirectImage_comp {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V)
    (d : proEtaleRingModuleDirectImage h (etaleOriginRing W Λ) (etaleOriginRing Z Λ)
          (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _)) ⋙
        proEtaleRingModuleDirectImage k (etaleOriginRing V Λ) (etaleOriginRing W Λ)
          (proEtaleRealizedCoefficientIso Λ k (Iso.refl _) (Iso.refl _)) ≅
      proEtaleRingModuleDirectImage (h ≫ k) (etaleOriginRing V Λ) (etaleOriginRing Z Λ)
        (proEtaleRealizedCoefficientIso Λ (h ≫ k) (Iso.refl _) (Iso.refl _)))
    (hd : ∀ (M : proEtaleRingModules Z (etaleOriginRing Z Λ)) (U : V.ProEt)
        (m : ((proEtaleRingModuleDirectImage h (etaleOriginRing W Λ)
          (etaleOriginRing Z Λ)
          (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _)) ⋙
          proEtaleRingModuleDirectImage k (etaleOriginRing V Λ) (etaleOriginRing W Λ)
          (proEtaleRealizedCoefficientIso Λ k (Iso.refl _) (Iso.refl _))).obj M).val.obj
          (Opposite.op U)),
      (d.hom.app M).val.app (Opposite.op U) m =
        M.val.map ((MorphismProperty.Over.pullbackComp h k).hom.app U).op m) :
    isoWhiskerLeft
        (proEtaleRingModuleDirectImage h (etaleOriginRing W Λ) (etaleOriginRing Z Λ)
          (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _)))
        (proEtaleConstantSectionsDirectImageIso Λ k) ≪≫
      isoWhiskerRight (proEtaleConstantSectionsDirectImageIso Λ h)
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) k) ≪≫
      isoWhiskerLeft (proEtaleConstantSections Λ Z)
        (ProEtale.lowerStarComp (ModuleCat.{u + 1} Λ) h k) =
    isoWhiskerRight d (proEtaleConstantSections Λ V) ≪≫
      proEtaleConstantSectionsDirectImageIso Λ (h ≫ k) := by
  apply Iso.ext
  ext M U m
  change (((ProEtale.lowerStarComp (ModuleCat.{u + 1} Λ) h k).hom.app
    ((proEtaleConstantSections Λ Z).obj M)).hom.app U) m =
      (d.hom.app M).val.app U m
  rw [ProEtale.lowerStarComp_hom_app_hom_app]
  exact (hd M U.unop m).symm

/-- The pullback comparison conjugate to the identity-on-sections direct-image comparison.
It uses the recorded adjunctions, hence fixes the choice of pullback comparison. -/
def proEtaleConstantSectionsPullbackIso {U V : Scheme.{u}} (h : U ⟶ V) :
    proEtaleRingModulePullback h (etaleOriginRing V Λ) (etaleOriginRing U Λ)
        (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _)) ⋙
      proEtaleConstantSections Λ U ≅
    proEtaleConstantSections Λ V ⋙ ProEtale.upperStar (ModuleCat.{u + 1} Λ) h := by
  let EV := (proEtaleConstantSections Λ V).asEquivalence
  let EU := (proEtaleConstantSections Λ U).asEquivalence
  let R := proEtaleRingModuleDirectImage h (etaleOriginRing V Λ) (etaleOriginRing U Λ)
    (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _))
  let D := ProEtale.lowerStar (ModuleCat.{u + 1} Λ) h
  let d : R ⋙ EV.functor ≅ EU.functor ⋙ D :=
    proEtaleConstantSectionsDirectImageIso Λ h
  let r : EU.inverse ⋙ R ≅ D ⋙ EV.inverse :=
    (Functor.rightUnitor _).symm ≪≫
      isoWhiskerLeft (EU.inverse ⋙ R) EV.unitIso ≪≫
      isoWhiskerRight (isoWhiskerLeft EU.inverse d) EV.inverse ≪≫
      isoWhiskerRight EU.counitIso (D ⋙ EV.inverse) ≪≫ Functor.leftUnitor _
  let adj := proEtaleRingModuleAdjunction h (etaleOriginRing V Λ) (etaleOriginRing U Λ)
    (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _))
  let adj' := ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h
  exact (conjugateIsoEquiv (EV.toAdjunction.comp adj')
    (adj.comp EU.toAdjunction)).symm r.symm

private theorem mate_of_equivalence_conjugate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (EV : A ≌ C) (EU : B ≌ D)
    (d : R ⋙ EV.functor ≅ EU.functor ⋙ R')
    (r : EU.inverse ⋙ R ≅ R' ⋙ EV.inverse)
    (hr : r = (Functor.rightUnitor _).symm ≪≫
      isoWhiskerLeft (EU.inverse ⋙ R) EV.unitIso ≪≫
      isoWhiskerRight (isoWhiskerLeft EU.inverse d) EV.inverse ≪≫
      isoWhiskerRight EU.counitIso (R' ⋙ EV.inverse) ≪≫ Functor.leftUnitor _) :
    mateEquiv adj adj'
        (TwoSquare.mk _ _ _ _
          ((conjugateIsoEquiv (EV.toAdjunction.comp adj')
            (adj.comp EU.toAdjunction)).symm r.symm).inv) =
      TwoSquare.mk _ _ _ _ d.hom := by
  apply (mateEquiv EU.toAdjunction EV.toAdjunction).injective
  apply TwoSquare.ext
  intro N
  rw [iterated_mateEquiv_conjugateEquiv]
  change ((conjugateEquiv (adj.comp EU.toAdjunction) (EV.toAdjunction.comp adj'))
    ((conjugateEquiv (adj.comp EU.toAdjunction) (EV.toAdjunction.comp adj')).symm
      r.hom)).app N = _
  rw [(conjugateEquiv (adj.comp EU.toAdjunction)
    (EV.toAdjunction.comp adj')).apply_symm_apply]
  subst r
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.comp_obj, Functor.comp_map,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_inv_app, mateEquiv_apply, TwoSquare.mk,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp]
  rfl

/-- The ordinary pullback comparison has exactly the specified direct-image mate. -/
theorem proEtaleConstantSectionsPullbackIso_mate {U V : Scheme.{u}} (h : U ⟶ V) :
    mateEquiv
      (proEtaleRingModuleAdjunction h (etaleOriginRing V Λ) (etaleOriginRing U Λ)
        (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _)))
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h)
      (TwoSquare.mk _ _ _ _ (proEtaleConstantSectionsPullbackIso Λ h).inv) =
    TwoSquare.mk _ _ _ _ (proEtaleConstantSectionsDirectImageIso Λ h).hom := by
  exact mate_of_equivalence_conjugate
    (proEtaleRingModuleAdjunction h (etaleOriginRing V Λ) (etaleOriginRing U Λ)
      (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _)))
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h)
    (proEtaleConstantSections Λ V).asEquivalence
    (proEtaleConstantSections Λ U).asEquivalence
    (proEtaleConstantSectionsDirectImageIso Λ h) _ rfl

/-- The explicit coordinate comparisons intertwine the ordinary module adjunctions. -/
theorem proEtaleConstantSectionsAdjunction {U V : Scheme.{u}} (h : U ⟶ V)
    (M : proEtaleRingModules V (etaleOriginRing V Λ))
    (N : proEtaleRingModules U (etaleOriginRing U Λ))
    (t : (proEtaleRingModulePullback h (etaleOriginRing V Λ) (etaleOriginRing U Λ)
      (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _))).obj M ⟶ N) :
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).homEquiv _ _
        ((proEtaleConstantSectionsPullbackIso Λ h).inv.app M ≫
          (proEtaleConstantSections Λ U).map t) =
      (proEtaleConstantSections Λ V).map
          ((proEtaleRingModuleAdjunction h (etaleOriginRing V Λ) (etaleOriginRing U Λ)
            (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _))).homEquiv _ _ t) ≫
        (proEtaleConstantSectionsDirectImageIso Λ h).hom.app N := by
  let adj := proEtaleRingModuleAdjunction h (etaleOriginRing V Λ) (etaleOriginRing U Λ)
    (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _))
  let adj' := ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h
  let b := TwoSquare.mk _ _ _ _ (proEtaleConstantSectionsPullbackIso Λ h).inv
  have hu := unit_mateEquiv adj adj' b M
  have hm := proEtaleConstantSectionsPullbackIso_mate Λ h
  change mateEquiv adj adj' b = _ at hm
  rw [hm] at hu
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  dsimp only [Functor.id_obj] at hu
  rw [← Category.assoc, ← hu, Category.assoc]
  have hn := (proEtaleConstantSectionsDirectImageIso Λ h).hom.naturality t
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← Functor.map_comp]

/-- The sectionwise direct-image comparison after total right derivation.
It uses the exactness of scalar restriction, not exactness of geometric direct image. -/
def proEtaleConstantSectionsDerivedDirectImage {U V : Scheme.{u}} (h : U ⟶ V) :
    proEtaleRingDerivedDirectImage h (etaleOriginRing V Λ) (etaleOriginRing U Λ)
        (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _)) ⋙
      (proEtaleConstantSections Λ V).mapDerivedCategory ≅
    (proEtaleConstantSections Λ U).mapDerivedCategory ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) h).rightDerivedFunctor :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
    (proEtaleRingModuleDirectImage h (etaleOriginRing V Λ) (etaleOriginRing U Λ)
      (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _)))
    (proEtaleConstantSections Λ V)).symm ≪≫
  Functor.rightDerivedFunctorNatIso (proEtaleConstantSectionsDirectImageIso Λ h) ≪≫
  Functor.rightDerivedFunctorCompIso (proEtaleConstantSections Λ U)
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) h) ≪≫
  isoWhiskerRight (proEtaleConstantSections Λ U).rightDerivedFunctorIsoMapDerivedCategory
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) h).rightDerivedFunctor

/-- Exact termwise descent of the adjunction-induced pullback comparison. -/
def proEtaleConstantSectionsDerivedPullbackIso {U V : Scheme.{u}} (h : U ⟶ V) :
    proEtaleRingDerivedPullback h (etaleOriginRing V Λ) (etaleOriginRing U Λ)
        (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _)) ⋙
      (proEtaleConstantSections Λ U).mapDerivedCategory ≅
    (proEtaleConstantSections Λ V).mapDerivedCategory ⋙
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) h).leftDerivedFunctor :=
  (Functor.mapDerivedCategoryCompIso
    (proEtaleRingModulePullback h (etaleOriginRing V Λ) (etaleOriginRing U Λ)
      (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _)))
    (proEtaleConstantSections Λ U)).symm ≪≫
  Functor.mapDerivedCategoryNatIso (proEtaleConstantSectionsPullbackIso Λ h) ≪≫
  Functor.mapDerivedCategoryCompIso (proEtaleConstantSections Λ V)
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ) h) ≪≫
  isoWhiskerLeft (proEtaleConstantSections Λ V).mapDerivedCategory
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) h).symm

/-- Derived scalar restriction is the inverse of derived realization, canonically. -/
def proEtaleConstantSectionsDerivedIsoInverse (T : Scheme.{u}) :
    (proEtaleConstantSections Λ T).mapDerivedCategory ≅
      (etaleOriginRealization T Λ).mapDerivedCategory.asEquivalence.inverse := by
  let E := (etaleOriginRealization T Λ).mapDerivedCategory.asEquivalence
  let S := (proEtaleConstantSections Λ T).mapDerivedCategory
  letI := proEtaleConstantSectionsUnit_isIso Λ T
  let η : 𝟭 _ ≅ E.functor ⋙ S :=
    (Functor.mapDerivedCategoryIdIso _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso (proEtaleConstantSectionsUnit Λ T)) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
  exact (Functor.leftUnitor _).symm ≪≫
    isoWhiskerRight E.counitIso.symm S ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft E.inverse η.symm ≪≫ Functor.rightUnitor _

/-- Restrict along the specified constant-ring identification, then undo realization.
Source: Stacks Tags 00YV and 03DA
(blueprint: lem-weil-pbc-realized-exchange-compatibility). -/
def proEtaleRealizedCoordinates (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (e : etaleOriginRing T Λ ≅ R) :
    DerivedCategory (proEtaleRingModules T R) ⥤
      DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} Λ)) := by
  letI := proEtaleRingRestrictScalars_preservesFiniteLimits e.hom
  letI := proEtaleRingRestrictScalars_preservesFiniteColimits e.hom
  exact (proEtaleRingRestrictScalars e.hom).mapDerivedCategory ⋙
    (proEtaleConstantSections Λ T).mapDerivedCategory

/-- The fixed-scalar coordinates detect isomorphisms of unbounded derived objects. -/
instance proEtaleRealizedCoordinates_reflectsIsomorphisms (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (e : etaleOriginRing T Λ ≅ R) :
    (proEtaleRealizedCoordinates Λ T R e).ReflectsIsomorphisms := by
  let F := proEtaleRingRestrictScalars e.hom
  let _ := proEtaleRingRestrictScalars_preservesFiniteLimits e.hom
  let _ := proEtaleRingRestrictScalars_preservesFiniteColimits e.hom
  have : F.ReflectsIsomorphisms := (proEtaleRingRestrictScalars_properties e.hom).2.2
  have : F.mapDerivedCategory.ReflectsIsomorphisms := by
    refine ⟨fun f _ ↦ ?_⟩
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso (F.map ((DerivedCategory.homologyFunctor _ n).map f)) :=
      (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) f).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ F
  change (F.mapDerivedCategory ⋙
    (proEtaleConstantSections Λ T).mapDerivedCategory).ReflectsIsomorphisms
  infer_instance

/-- Conjugating the constant comparison gives the required coefficient square. -/
theorem proEtaleRealizedCoefficientIso_square {U V : Scheme.{u}} (h : U ⟶ V)
    {RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1}}
    {RU : Sheaf (ProEt.topology U) CommRingCat.{u + 1}}
    (eV : etaleOriginRing V Λ ≅ RV) (eU : etaleOriginRing U Λ ≅ RU) :
    (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _)).hom ≫ eU.hom =
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map eV.hom ≫
        (proEtaleRealizedCoefficientIso Λ h eV eU).hom := by
  simp only [proEtaleRealizedCoefficientIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.refl_inv, Iso.refl_hom, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

attribute [local instance] proEtaleRingRestrictScalars_preservesFiniteLimits
  proEtaleRingRestrictScalars_preservesFiniteColimits

/-- Derived direct image commutes with the specified realized coefficient coordinates. -/
def proEtaleRealizedDirectImageIso {U V : Scheme.{u}} (h : U ⟶ V)
    {RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1}}
    {RU : Sheaf (ProEt.topology U) CommRingCat.{u + 1}}
    (eV : etaleOriginRing V Λ ≅ RV) (eU : etaleOriginRing U Λ ≅ RU) :
    proEtaleRingDerivedDirectImage h RV RU (proEtaleRealizedCoefficientIso Λ h eV eU) ⋙
      proEtaleRealizedCoordinates Λ V RV eV ≅
    proEtaleRealizedCoordinates Λ U RU eU ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) h).rightDerivedFunctor :=
  isoWhiskerRight
    (proEtaleRingRestrictionDerivedDirectImage h (etaleOriginRing V Λ) RV
      (etaleOriginRing U Λ) RU eV.hom eU.hom
      (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _))
      (proEtaleRealizedCoefficientIso Λ h eV eU)
      (proEtaleRealizedCoefficientIso_square Λ h eV eU))
    (proEtaleConstantSections Λ V).mapDerivedCategory ≪≫
  isoWhiskerLeft (proEtaleRingRestrictScalars eU.hom).mapDerivedCategory
    (proEtaleConstantSectionsDerivedDirectImage Λ h)

/-- Derived pullback commutes with the specified realized coefficient coordinates. -/
def proEtaleRealizedPullbackIso {U V : Scheme.{u}} (h : U ⟶ V)
    {RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1}}
    {RU : Sheaf (ProEt.topology U) CommRingCat.{u + 1}}
    (eV : etaleOriginRing V Λ ≅ RV) (eU : etaleOriginRing U Λ ≅ RU) :
    proEtaleRingDerivedPullback h RV RU (proEtaleRealizedCoefficientIso Λ h eV eU) ⋙
      proEtaleRealizedCoordinates Λ U RU eU ≅
    proEtaleRealizedCoordinates Λ V RV eV ⋙
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) h).leftDerivedFunctor :=
  isoWhiskerRight
    (proEtaleRingRestrictionDerivedPullback h (etaleOriginRing V Λ) RV
      (etaleOriginRing U Λ) RU eV.hom eU.hom
      (proEtaleRealizedCoefficientIso Λ h (Iso.refl _) (Iso.refl _))
      (proEtaleRealizedCoefficientIso Λ h eV eU)
      (proEtaleRealizedCoefficientIso_square Λ h eV eU))
    (proEtaleConstantSections Λ U).mapDerivedCategory ≪≫
  isoWhiskerLeft (proEtaleRingRestrictScalars eV.hom).mapDerivedCategory
    (proEtaleConstantSectionsDerivedPullbackIso Λ h)

attribute [local irreducible] proEtaleRealizedCoefficientIso proEtaleRealizedCoordinates
  proEtaleConstantSections proEtaleRingModulePullback proEtaleRingModuleDirectImage

/-- Source comparison for exchange, with the specified edge comparisons. -/
def proEtaleRealizedExchangeSourceIso {X Y' Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RY' : Sheaf (ProEt.topology Y') CommRingCat.{u + 1})
    (eX : etaleOriginRing X Λ ≅ RX) (eY : etaleOriginRing Y Λ ≅ RY)
    (eY' : etaleOriginRing Y' Λ ≅ RY') :
    proEtaleRingDerivedDirectImage f RY RX (proEtaleRealizedCoefficientIso Λ f eY eX) ⋙
        proEtaleRingDerivedPullback g RY RY' (proEtaleRealizedCoefficientIso Λ g eY eY') ⋙
        proEtaleRealizedCoordinates Λ Y' RY' eY' ≅
      proEtaleRealizedCoordinates Λ X RX eX ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor :=
  isoWhiskerLeft
    (proEtaleRingDerivedDirectImage f RY RX (proEtaleRealizedCoefficientIso Λ f eY eX))
    (proEtaleRealizedPullbackIso Λ g eY eY') ≪≫
  isoWhiskerRight (proEtaleRealizedDirectImageIso Λ f eY eX)
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor

/-- Target comparison for exchange, with the specified edge comparisons. -/
def proEtaleRealizedExchangeTargetIso {X' X Y' : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (RX' : Sheaf (ProEt.topology X') CommRingCat.{u + 1})
    (RY' : Sheaf (ProEt.topology Y') CommRingCat.{u + 1})
    (eX : etaleOriginRing X Λ ≅ RX) (eX' : etaleOriginRing X' Λ ≅ RX')
    (eY' : etaleOriginRing Y' Λ ≅ RY') :
    proEtaleRingDerivedPullback g' RX RX' (proEtaleRealizedCoefficientIso Λ g' eX eX') ⋙
        proEtaleRingDerivedDirectImage f' RY' RX'
          (proEtaleRealizedCoefficientIso Λ f' eY' eX') ⋙
        proEtaleRealizedCoordinates Λ Y' RY' eY' ≅
      proEtaleRealizedCoordinates Λ X RX eX ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').leftDerivedFunctor ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f').rightDerivedFunctor :=
  isoWhiskerLeft
    (proEtaleRingDerivedPullback g' RX RX' (proEtaleRealizedCoefficientIso Λ g' eX eX'))
    (proEtaleRealizedDirectImageIso Λ f' eY' eX') ≪≫
  isoWhiskerRight (proEtaleRealizedPullbackIso Λ g' eX eX')
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f').rightDerivedFunctor

/-- The canonical ambient mate agrees with the fixed-scalar mate under the explicit
endpoint comparisons.
Source: Stacks Tags 00YV, 03D2, 07A7, 0D6D and 0D6E
(blueprint: lem-weil-pbc-realized-exchange-compatibility).

Proof: the sectionwise direct-image comparison proEtaleConstantSectionsDirectImageIso
is the identity on sections. The structural coefficient map preserves constant scalars,
as proEtaleConstantCoefficient_scalar proves. Its conjugate under the recorded module
adjunctions is proEtaleConstantSectionsPullbackIso. The theorem
proEtaleConstantSectionsDirectImage_comp proves compatibility with
ordinary composition: both direct-image composites act on a section by the same
fibre-product pasting map. The theorem proEtaleConstantSectionsPullbackIso_mate and
its hom-equivalence form proEtaleConstantSectionsAdjunction prove the ordinary
adjunction comparison. Conjugation of the composition equality then identifies the
ordinary pullback comparison, using conjugateEquiv_comp, conjugateEquiv_whiskerLeft,
conjugateEquiv_whiskerRight and the fixed-scalar conjugateIsoEquiv_upperStarComp.
For general e, proEtaleRealizedCoefficientIso_square gives the ring-sheaf square, and
proEtaleRingSheafChangeAdjunction identifies both adjunctions after restriction.
The ordinary composition equality descends termwise. On flat-term K-flat complexes
it is exactly the normalization defining proEtaleCanonicalDerivedPullbackComparison;
naturality along resolution quasi-isomorphisms determines its value everywhere.
The constant inverse-image comparison is likewise coherent with composition.
Thus the four proEtaleRealizedPullbackIso comparisons identify the actual ringed
pullback square with ProEtale.leftDerivedUpperStarSquareIso. Total right derivation
of the sectionwise direct-image comparison gives proEtaleRealizedDirectImageIso.
Uniqueness of right derivation and the unit normalization show that it is the mate
of the pullback comparison under the specified derived adjunctions. Finally expand
the unit--square--counit formula for the two ambient exchanges. The pullback square,
unit and counit equalities just proved give the displayed equality, with precisely
proEtaleRealizedExchangeSourceIso and proEtaleRealizedExchangeTargetIso as endpoints.
This is equality of natural transformations for all objects, independent of any
properness, boundedness, etale antecedent, or invertibility assumption. -/
theorem proEtaleRealizedExchange_compatibility
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X' : Sheaf (ProEt.topology X') CommRingCat.{u + 1})
    (R_Y' : Sheaf (ProEt.topology Y') CommRingCat.{u + 1})
    (eX : etaleOriginRing X Λ ≅ R_X) (eY : etaleOriginRing Y Λ ≅ R_Y)
    (eX' : etaleOriginRing X' Λ ≅ R_X') (eY' : etaleOriginRing Y' Λ ≅ R_Y')
    (hcoeff : HEq
      (proEtaleRingCompositeCoefficients g' f R_Y R_X R_X'
        (proEtaleRealizedCoefficientIso Λ f eY eX)
        (proEtaleRealizedCoefficientIso Λ g' eX eX'))
      (proEtaleRingCompositeCoefficients f' g R_Y R_Y' R_X'
        (proEtaleRealizedCoefficientIso Λ g eY eY')
        (proEtaleRealizedCoefficientIso Λ f' eY' eX'))) :
    Functor.whiskerRight
        (proEtaleAmbientRingedExchange sq R_X R_Y R_X' R_Y'
          (proEtaleRealizedCoefficientIso Λ f eY eX)
          (proEtaleRealizedCoefficientIso Λ g eY eY')
          (proEtaleRealizedCoefficientIso Λ g' eX eX')
          (proEtaleRealizedCoefficientIso Λ f' eY' eX') hcoeff)
        (proEtaleRealizedCoordinates Λ Y' R_Y' eY') ≫
      (proEtaleRealizedExchangeTargetIso Λ g' f' R_X R_X' R_Y' eX eX' eY').hom =
    (proEtaleRealizedExchangeSourceIso Λ f g R_X R_Y R_Y' eX eY eY').hom ≫
      Functor.whiskerLeft (proEtaleRealizedCoordinates Λ X R_X eX)
        (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  sorry

end AlgebraicGeometry.Scheme
