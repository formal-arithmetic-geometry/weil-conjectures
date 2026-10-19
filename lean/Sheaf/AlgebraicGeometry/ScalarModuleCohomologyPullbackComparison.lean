/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups U2, B2
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.FieldScalarRestrictionInjectives
import Mathlib.Algebra.Homology.ConcreteCategory
import WeilConjectures.CategoryTheory.ExactFunctorResolutionCocycle

/-! # Scalar and module pullback comparison

Source: Stacks Project, Cohomology, Tag 01F7.
-/

@[expose] public section
universe w v₁ v₂ u₁ u₂ e₁ e₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Sheaf.monoidalCategory
variable {k : Type w} [Field k] {X Y : Scheme.{w}}
private theorem scalar_hasExt : HasExt.{w + 1} (KSheaf X k) := HasExt.standard _
attribute [local instance] scalar_hasExt

-- Restriction to k-vector spaces preserves injectivity and commutes with direct image.
private theorem scalar_injective (f : X ⟶ Spec (CommRingCat.of k)) :
    (scalarFunctor f).PreservesInjectiveObjects := by
  have hi := SheafOfModules.fieldScalarRestriction_preservesInjectives
    X.toTopCat X.ringCatSheaf
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom)
  refine ⟨fun {I} hI ↦ ?_⟩
  let q := (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom)
  let S := SheafOfModules.forgetToSheafModuleCat.{w} X.ringCatSheaf (op ⊤)
    isTerminalTop.op ⋙ sheafCompose (Opens.grothendieckTopology X)
      (ModuleCat.restrictScalars q)
  have e : scalarSheaf f I ≅ S.obj I :=
    ObjectProperty.isoMk _ (NatIso.ofComponents
      (fun U ↦ ModuleCat.restrictScalarsComp'App q
        (X.ringCatSheaf.obj.map (isTerminalTop.op.to U)).hom (scalarMap f U.unop)
        (by unfold scalarMap; rfl) (I.val.obj U)) (by
          intro U V i
          ext x
          rfl))
  exact Injective.of_iso e.symm (hi.injective_obj hI)

private theorem scalar_map_pullback (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (a : Y ⟶ X) (h : a ≫ f = g)
    (U : X.Opens) (r : k) :
    (a.app U).hom (scalarMap f U r) = scalarMap g (a ⁻¹ᵁ U) r := by
  have hn := a.naturality (homOfLE (le_top (a := U))).op
  have ht := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop] at ht
  simp only [scalarMap, RingHom.comp_apply]
  change (X.presheaf.map (homOfLE (le_top (a := U))).op ≫ a.app U)
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop) r) = _
  rw [hn]
  change (a.appTop ≫ Y.presheaf.map (homOfLE (le_top (a := a ⁻¹ᵁ U))).op)
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop) r) = _
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫ a.appTop ≫
    Y.presheaf.map (homOfLE (le_top (a := a ⁻¹ᵁ U))).op) r = _
  rw [← Category.assoc f.appTop, ht]
  rfl

private abbrev scalarPushforward (a : Y ⟶ X) : KSheaf Y k ⥤ KSheaf X k :=
  (Opens.map a.base).sheafPushforwardContinuous (ModuleCat.{w} k)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)

private def scalarPushforwardIso (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (a : Y ⟶ X) (h : a ≫ f = g) :
    pushforward a ⋙ scalarFunctor f ≅ scalarFunctor g ⋙ scalarPushforward a := by
  refine NatIso.ofComponents (fun F ↦ ?_) ?_
  · refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦ ?_) ?_)
    · letI : Module k (((pushforward a).obj F).val.obj U) :=
        Module.compHom _ (scalarMap f U.unop)
      letI : Module k (F.val.obj ((Opens.map a.base).op.obj U)) :=
        Module.compHom _ (scalarMap g (a ⁻¹ᵁ U.unop))
      refine {
        hom := ModuleCat.ofHom ?_
        inv := ModuleCat.ofHom ?_
        hom_inv_id := ?_
        inv_hom_id := ?_ }
      · refine { toFun := fun x ↦ x, map_add' := fun _ _ ↦ rfl, map_smul' := ?_ }
        intro r s
        change (a.app U.unop).hom (scalarMap f U.unop r) •
            (show F.val.obj ((Opens.map a.base).op.obj U) from s) =
          scalarMap g (a ⁻¹ᵁ U.unop) r •
            (show F.val.obj ((Opens.map a.base).op.obj U) from s)
        rw [scalar_map_pullback f g a h]
      · refine { toFun := fun x ↦ x, map_add' := fun _ _ ↦ rfl, map_smul' := ?_ }
        intro r s
        change scalarMap g (a ⁻¹ᵁ U.unop) r •
            (show F.val.obj ((Opens.map a.base).op.obj U) from s) =
          (a.app U.unop).hom (scalarMap f U.unop r) •
            (show F.val.obj ((Opens.map a.base).op.obj U) from s)
        rw [scalar_map_pullback f g a h]
      · ext x
        rfl
      · ext x
        rfl
    · intro U V i
      ext x
      rfl
  · intro F G b
    ext U x
    rfl

-- Transport a resolution along an exact functor which preserves injectives.
private def mapResolution
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [S.PreservesInjectiveObjects] {F : C} (I : InjectiveResolution F) :
    InjectiveResolution (S.obj F) where
  cocomplex := (S.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  injective n := S.injective_obj _
  ι := (HomologicalComplex.singleMapHomologicalComplex S (.up ℕ) 0).inv.app F ≫
    (S.mapHomologicalComplex (.up ℕ)).map I.ι

-- Transport a resolution cocycle, then precompose its source using Mathlib.
private theorem extMk_map
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [HasExt.{e₁} C] [HasExt.{e₂} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A B : C} {A' B' : D} (α : A' ⟶ L.obj A)
    (R : InjectiveResolution B) (R' : InjectiveResolution B') (v : L.obj B ⟶ B')
    (φ : (L.mapHomologicalComplex (.up ℕ)).obj R.cocomplex ⟶ R'.cocomplex)
    (hφ : L.map (R.ι.f 0) ≫ φ.f 0 = v ≫ R'.ι.f 0)
    (n : ℕ) (b : A ⟶ R.cocomplex.X n)
    (hb : b ≫ R.cocomplex.d n (n + 1) = 0) :
    ((Abelian.Ext.mk₀ α).comp ((R.extMk b (n + 1) rfl hb).mapExactFunctor L)
      (zero_add n)).comp (Abelian.Ext.mk₀ v) (add_zero n) =
      R'.extMk (α ≫ L.map b ≫ φ.f n) (n + 1) rfl (by
        rw [Category.assoc, Category.assoc]
        erw [φ.comm, ← L.map_comp_assoc, hb, L.map_zero, zero_comp, comp_zero]) := by
  have hc : (L.map b ≫ φ.f n) ≫ R'.cocomplex.d n (n + 1) = 0 := by
    rw [Category.assoc, φ.comm]
    erw [← L.map_comp_assoc, hb, L.map_zero, zero_comp]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [exactFunctor_resolution_cocycle L v R R' φ hφ n b hb hc]
  exact R'.mk₀_comp_extMk (L.map b ≫ φ.f n) (n + 1) rfl hc α

private theorem mapResolution_zero
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [S.PreservesInjectiveObjects] {F : C} (I : InjectiveResolution F) :
    (mapResolution S I).ι.f 0 = S.map (I.ι.f 0) := by
  simp [mapResolution, HomologicalComplex.singleMapHomologicalComplex_inv_app_self]

-- Evaluation at 1 identifies maps from either unit object with global sections.
private def moduleSectionEquiv (F : SheafOfModules.{w} X.ringCatSheaf) :
    (SheafOfModules.unit X.ringCatSheaf ⟶ F) ≃+ F.val.obj (op ⊤) where
  toFun φ := φ.val.app (op ⊤) (1 : Γ(X, ⊤))
  invFun s := F.unitHomEquiv.symm (F.val.sectionsMk
    (fun U ↦ F.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s)
    (by intro U V i; rw [← PresheafOfModules.map_comp_apply]; rfl))
  left_inv φ := by
    apply F.unitHomEquiv.injective
    apply Subtype.ext
    funext U
    simp only [Equiv.apply_symm_apply]
    exact (F.unitHomEquiv φ).property _
  right_inv s := by
    change (F.unitHomEquiv (F.unitHomEquiv.symm _)).val (op ⊤) = s
    rw [Equiv.apply_symm_apply]
    change F.val.map (𝟙 _) s = s
    simp
  map_add' φ ψ := rfl

private def scalarSection (M : KSheaf X k) (φ : 𝟙_ (KSheaf X k) ⟶ M) :=
  ((constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{w} k)
    isTerminalTop).homEquiv _ _ (constantScalarUnitIso.hom ≫ φ)) (1 : k)

private theorem scalarSection_injective (M : KSheaf X k) :
    Function.Injective (scalarSection M) := by
  intro φ ψ h
  apply (cancel_epi constantScalarUnitIso.hom).mp
  apply ((constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{w} k)
    isTerminalTop).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply (LinearMap.ringLmapEquivSelf k k _).injective
  exact h

private theorem scalarSection_module (f : X ⟶ Spec (CommRingCat.of k))
    {F : SheafOfModules.{w} X.ringCatSheaf} (φ : SheafOfModules.unit X.ringCatSheaf ⟶ F) :
    scalarSection (scalarSheaf f F) (scalarUnitMorphism f ≫ scalarHom f φ) =
      φ.val.app (op ⊤) (1 : Γ(X, ⊤)) := by
  unfold scalarSection scalarUnitMorphism
  rw [Category.assoc, Iso.hom_inv_id_assoc, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply]
  change φ.val.app (op ⊤) (scalarMap f ⊤ 1) = _
  rw [map_one]

private theorem module_enoughInjectives : EnoughInjectives (SheafOfModules.{w} X.ringCatSheaf) :=
  (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2

attribute [local instance] module_enoughInjectives

private theorem module_hasExt : HasExt.{w} (SheafOfModules.{w} X.ringCatSheaf) :=
  hasExt_of_enoughInjectives.{w, w, w + 1} (SheafOfModules.{w} X.ringCatSheaf)

attribute [local instance] module_enoughInjectives module_hasExt
  RingedSpace.globalSectionsFunctor_additive

private theorem scalarSection_comp {M N : KSheaf X k}
    (φ : 𝟙_ (KSheaf X k) ⟶ M) (b : M ⟶ N) :
    scalarSection N (φ ≫ b) = b.hom.app (op ⊤) (scalarSection M φ) := by
  unfold scalarSection
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  rfl

private theorem homotopy_zero_cycles
    {C : Type*} [Category* C] [Preadditive C]
    {K L : CochainComplex C ℕ} {u v : K ⟶ L}
    (H : Homotopy u v) {B : C} (b : B ⟶ K.X 0) (hb : b ≫ K.d 0 1 = 0) :
    b ≫ u.f 0 = b ≫ v.f 0 := by
  rw [H.comm 0, dNext_eq H.hom (show (ComplexShape.up ℕ).Rel 0 1 from rfl),
    prevD_eq_zero H.hom 0 (by decide)]
  simp [Preadditive.comp_add, ← Category.assoc, hb]

-- The chosen constant-sheaf pullback isomorphism transports the same global section.
private theorem scalarSection_pullback (a : Y ⟶ X)
    {M : KSheaf X k} {N : KSheaf Y k} (b : 𝟙_ (KSheaf X k) ⟶ M)
    (ψ : (scalarInverseImage a).obj M ⟶ N) :
    scalarSection N ((scalarInverseUnitIso a).inv ≫ (scalarInverseImage a).map b ≫ ψ) =
      (((Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).homEquiv _ _ ψ).hom.app
          (op ⊤) (scalarSection M b) := by
  let A := constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{w} k)
    isTerminalTop
  let B := constantSheafAdj (Opens.grothendieckTopology Y) (ModuleCat.{w} k)
    isTerminalTop
  let adj := (Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let e := (Opens.map a.base).sheafPushforwardContinuousCompSheafSectionsObjIso
    (ModuleCat.{w} k) (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) (op ⊤)
  let E := (Opens.map a.base).constantSheafsheafPullbackIso
    (ModuleCat.{w} k) (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
    isTerminalTop isTerminalTop
  have he (t : (scalarInverseImage a).obj
      ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)) ⟶ N) :
      B.homEquiv _ _ (E.inv.app (ModuleCat.of k k) ≫ t) =
        A.homEquiv _ _ (adj.homEquiv _ _ t) ≫ e.hom.app N := by
    rw [Adjunction.homEquiv_naturality_right]
    change B.homEquiv _ _
      ((B.leftAdjointUniq ((A.comp adj).ofNatIsoRight e)).hom.app _) ≫ _ = _
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    erw [← Adjunction.homEquiv_unit]
  unfold scalarSection scalarInverseUnitIso
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc,
    Iso.hom_inv_id_assoc]
  have hh := he ((scalarInverseImage a).map (constantScalarUnitIso.hom ≫ b) ≫ ψ)
  erw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at hh
  dsimp [e, Functor.sheafPushforwardContinuousCompSheafSectionsObjIso] at hh
  simp only [Category.comp_id] at hh
  have hv := ConcreteCategory.congr_hom hh (1 : k)
  erw [(scalarInverseImage a).map_comp] at hv
  exact hv

private abbrev scalarAdj (a : Y ⟶ X) :
    scalarInverseImage (k := k) a ⊣ scalarPushforward a :=
  (Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)

private theorem scalarPushforward_additive (a : Y ⟶ X) :
    (scalarPushforward (k := k) a).Additive where
  map_add := by intros; ext U x; rfl

private theorem scalarPushforward_injective (a : Y ⟶ X) :
    (scalarPushforward (k := k) a).PreservesInjectiveObjects := by
  have : (scalarInverseImage (k := k) a).PreservesMonomorphisms := by infer_instance
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (scalarAdj a)

private theorem scalar_coefficient_adj (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (a : Y ⟶ X) (h : a ≫ f = g)
    (F : SheafOfModules.{w} X.ringCatSheaf) :
    (scalarAdj a).homEquiv _ _ (scalarPullbackCoefficient f g a h F) =
      (scalarFunctor f).map
        ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app F) ≫
        (scalarPushforwardIso f g a h).hom.app ((tensorPullback a).obj F) := by
  unfold scalarPullbackCoefficient
  ext U s
  exact Classical.choose_spec (exists_scalarPullbackCoefficient f g a h F) U.unop s

private def adj_complex
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] (adj : L ⊣ R)
    {K : CochainComplex C ℕ} {I : CochainComplex D ℕ}
    (b : K ⟶ (R.mapHomologicalComplex (.up ℕ)).obj I) :
    (L.mapHomologicalComplex (.up ℕ)).obj K ⟶ I where
  f n := (adj.homEquiv _ _).symm (b.f n)
  comm' i j _ := by
    apply (adj.homEquiv _ _).injective
    change adj.homEquiv _ _ ((adj.homEquiv _ _).symm (b.f i) ≫ I.d i j) =
      adj.homEquiv _ _ (L.map (K.d i j) ≫ (adj.homEquiv _ _).symm (b.f j))
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact b.comm i j

private theorem adj_complex_app
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] (adj : L ⊣ R)
    {K : CochainComplex C ℕ} {I : CochainComplex D ℕ}
    (b : K ⟶ (R.mapHomologicalComplex (.up ℕ)).obj I) (n : ℕ) :
    adj.homEquiv _ _ ((adj_complex adj b).f n) = b.f n := by
  exact (adj.homEquiv _ _).apply_symm_apply _

private def scalarUnitHomEquiv (f : X ⟶ Spec (CommRingCat.of k))
    (F : SheafOfModules.{w} X.ringCatSheaf) :
    (SheafOfModules.unit X.ringCatSheaf ⟶ F) ≃
      (𝟙_ (KSheaf X k) ⟶ scalarSheaf f F) where
  toFun b := scalarUnitMorphism f ≫ scalarHom f b
  invFun b := (moduleSectionEquiv F).symm (scalarSection (scalarSheaf f F) b)
  left_inv b := by
    apply (moduleSectionEquiv F).injective
    rw [AddEquiv.apply_symm_apply, scalarSection_module]
    rfl
  right_inv b := by
    apply scalarSection_injective
    rw [scalarSection_module]
    exact (moduleSectionEquiv F).apply_symm_apply _

private theorem scalarUnitHomEquiv_closed (f : X ⟶ Spec (CommRingCat.of k))
    {F G : SheafOfModules.{w} X.ringCatSheaf} (d : F ⟶ G)
    (b : 𝟙_ (KSheaf X k) ⟶ scalarSheaf f F)
    (hb : b ≫ (scalarFunctor f).map d = 0) :
    (scalarUnitHomEquiv f F).symm b ≫ d = 0 := by
  apply (moduleSectionEquiv G).injective
  change d.val.app (op ⊤)
    (moduleSectionEquiv F ((scalarUnitHomEquiv f F).symm b)) = 0
  change d.val.app (op ⊤)
    (moduleSectionEquiv F ((moduleSectionEquiv F).symm (scalarSection (scalarSheaf f F) b))) = 0
  rw [AddEquiv.apply_symm_apply]
  have hh := congrArg (scalarSection (scalarSheaf f G)) hb
  rw [scalarSection_comp] at hh
  exact hh

private theorem modulePushforward_additive (a : Y ⟶ X) : (pushforward a).Additive where
  map_add := by intros; ext U s; rfl

attribute [local instance] scalarPushforward_additive modulePushforward_additive

private def scalarPushforwardComplexIso
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (a : Y ⟶ X) (h : a ≫ f = g)
    (I : CochainComplex (SheafOfModules.{w} Y.ringCatSheaf) ℕ) :
    ((scalarFunctor f).mapHomologicalComplex (.up ℕ)).obj
        (((pushforward a).mapHomologicalComplex (.up ℕ)).obj I) ≅
      ((scalarPushforward a).mapHomologicalComplex (.up ℕ)).obj
        (((scalarFunctor g).mapHomologicalComplex (.up ℕ)).obj I) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (scalarPushforwardIso f g a h).app (I.X n))
    (fun i j _ ↦ ((scalarPushforwardIso f g a h).hom.naturality (I.d i j)).symm)

private abbrev moduleSections (X : Scheme.{w}) :=
  RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{w}

private abbrev scalarSections (X : Scheme.{w}) (k : Type w) [Field k] :
    KSheaf X k ⥤ AddCommGrpCat.{w} :=
  (sheafSections (Opens.grothendieckTopology X) (ModuleCat.{w} k)).obj (op ⊤) ⋙
    forget₂ _ AddCommGrpCat.{w}

private theorem scalarSections_additive (X : Scheme.{w}) (k : Type w) [Field k] :
    (scalarSections X k).Additive where
  map_add := by intros; rfl

attribute [local instance] scalarSections_additive

private theorem choices_sections_identity
    (a : Y ⟶ X) {F : SheafOfModules.{w} X.ringCatSheaf}
    {G : SheafOfModules.{w} Y.ringCatSheaf} {η : F ⟶ (pushforward a).obj G}
    (D : ModuleCohomologyFMapData a F G η) :
    D.a.inv = 𝟙 _ := by
  ext n s
  rw [D.sections]
  change (presheaf (D.I.cocomplex.X n)).map (𝟙 _) s = s
  simp

private theorem map_augmentation_closed
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Preadditive D] [Preadditive E]
    (L : C ⥤ D) (R : D ⥤ E) [L.Additive] [R.Additive]
    {F : C} (I : InjectiveResolution F) :
    R.map (L.map (I.ι.f 0)) ≫ R.map (L.map (I.cocomplex.d 0 1)) = 0 := by
  rw [← R.map_comp, ← L.map_comp, I.ι_f_zero_comp_complex_d, L.map_zero, R.map_zero]

private theorem homotopy_inverse
    {C : Type*} [Category C] [Abelian C] {K L : CochainComplex C ℕ}
    [∀ n, Injective (K.X n)] [∀ n, Injective (L.X n)] (l : K ⟶ L) [QuasiIso l] :
    ∃ r : L ⟶ K, Nonempty (Homotopy (l ≫ r) (𝟙 K)) ∧
      Nonempty (Homotopy (r ≫ l) (𝟙 L)) := by
  obtain ⟨⟨u, r, H₁, H₂⟩, hu⟩ :=
    (CochainComplex.quasiIso_iff_of_injective l).mp inferInstance
  dsimp at hu
  subst u
  exact ⟨r, ⟨H₁⟩, ⟨H₂⟩⟩

set_option maxHeartbeats 800000 in
-- The injective comparison involves the natural identifications of three complex functors.
private theorem scalar_comparison
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (a : Y ⟶ X) (h : a ≫ f = g) (F : SheafOfModules.{w} X.ringCatSheaf)
    (D : ModuleCohomologyFMapData a F ((tensorPullback a).obj F)
      ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app F)) :
    ∃ b : ((scalarFunctor f).mapHomologicalComplex (.up ℕ)).obj D.J.cocomplex ⟶
        ((scalarPushforward a).mapHomologicalComplex (.up ℕ)).obj
          (((scalarFunctor g).mapHomologicalComplex (.up ℕ)).obj D.I.cocomplex),
      (scalarFunctor f).map (D.J.ι.f 0) ≫ b.f 0 =
        (scalarAdj a).homEquiv _ _ (scalarPullbackCoefficient f g a h F) ≫
          (scalarPushforward a).map ((scalarFunctor g).map (D.I.ι.f 0)) ∧
      Nonempty (Homotopy
        (b ≫ (scalarPushforwardComplexIso f g a h D.I.cocomplex).inv ≫
          ((scalarFunctor f).mapHomologicalComplex (.up ℕ)).map D.lambda)
        (((scalarFunctor f).mapHomologicalComplex (.up ℕ)).map D.β)) := by
  have := scalar_injective f
  have := scalar_injective g
  have := scalarPushforward_injective (k := k) a
  let S := (scalarFunctor f).mapHomologicalComplex (.up ℕ)
  let e := scalarPushforwardComplexIso f g a h D.I.cocomplex
  let l := e.inv ≫ S.map D.lambda
  have : QuasiIso D.lambda := D.quasiIso
  have : QuasiIso l := by dsimp [l, S]; infer_instance
  have : ∀ n, Injective
      ((((scalarPushforward a).mapHomologicalComplex (.up ℕ)).obj
        (((scalarFunctor g).mapHomologicalComplex (.up ℕ)).obj D.I.cocomplex)).X n) := by
    intro n
    exact (scalarPushforward a).injective_obj_of_injective
      ((scalarFunctor g).injective_obj_of_injective (D.I.injective n))
  have : ∀ n, Injective ((S.obj D.K).X n) := by
    intro n
    exact (scalarFunctor f).injective_obj_of_injective (D.injective n)
  obtain ⟨r, ⟨H₁⟩, ⟨H₂⟩⟩ := homotopy_inverse l
  let b := S.map D.β ≫ r
  refine ⟨b, ?_, ?_⟩
  · rw [scalar_coefficient_adj]
    change (scalarFunctor f).map (D.J.ι.f 0) ≫
      (scalarFunctor f).map (D.β.f 0) ≫ r.f 0 = _
    erw [← (scalarFunctor f).map_comp_assoc, D.compatible]
    simp only [Functor.map_comp, Category.assoc]
    have hz : (scalarPushforward a).map ((scalarFunctor g).map (D.I.ι.f 0)) ≫
        (((scalarPushforward a).mapHomologicalComplex (.up ℕ)).obj
          (((scalarFunctor g).mapHomologicalComplex (.up ℕ)).obj D.I.cocomplex)).d 0 1 = 0 := by
      change (scalarPushforward a).map ((scalarFunctor g).map (D.I.ι.f 0)) ≫
        (scalarPushforward a).map ((scalarFunctor g).map (D.I.cocomplex.d 0 1)) = 0
      exact map_augmentation_closed (scalarFunctor g) (scalarPushforward a) D.I
    have hh := homotopy_zero_cycles (C := KSheaf X k) H₁
      ((scalarPushforward a).map ((scalarFunctor g).map (D.I.ι.f 0))) hz
    dsimp only [l, HomologicalComplex.comp_f] at hh
    have hn := (scalarPushforwardIso f g a h).hom.naturality (D.I.ι.f 0)
    change (scalarFunctor f).map ((pushforward a).map (D.I.ι.f 0)) ≫
      (scalarPushforwardIso f g a h).hom.app (D.I.cocomplex.X 0) =
        (scalarPushforwardIso f g a h).hom.app ((tensorPullback a).obj F) ≫
          (scalarPushforward a).map ((scalarFunctor g).map (D.I.ι.f 0)) at hn
    have hn' : (scalarFunctor f).map ((pushforward a).map (D.I.ι.f 0)) =
        (scalarPushforwardIso f g a h).hom.app ((tensorPullback a).obj F) ≫
          (scalarPushforward a).map ((scalarFunctor g).map (D.I.ι.f 0)) ≫
            (scalarPushforwardIso f g a h).inv.app (D.I.cocomplex.X 0) := by
      rw [← cancel_mono ((scalarPushforwardIso f g a h).hom.app (D.I.cocomplex.X 0))]
      simp only [Category.assoc, Iso.inv_hom_id_app]
      exact hn
    change (scalarPushforward a).map ((scalarFunctor g).map (D.I.ι.f 0)) ≫
      ((scalarPushforwardIso f g a h).inv.app (D.I.cocomplex.X 0) ≫
        (scalarFunctor f).map (D.lambda.f 0)) ≫ r.f 0 =
          (scalarPushforward a).map ((scalarFunctor g).map (D.I.ι.f 0)) ≫ 𝟙 _ at hh
    simp only [Category.assoc, Category.comp_id] at hh
    refine (congrArg (fun z ↦
      (scalarFunctor f).map
        ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app F) ≫
        z ≫ (scalarFunctor f).map (D.lambda.f 0) ≫ r.f 0) hn').trans ?_
    simpa only [Category.assoc] using congrArg (fun z ↦
      (scalarFunctor f).map
        ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app F) ≫
        (scalarPushforwardIso f g a h).hom.app ((tensorPullback a).obj F) ≫ z) hh
  · have hh := H₂.compLeft (S.map D.β)
    refine ⟨?_⟩
    dsimp only [b]
    change Homotopy ((S.map D.β ≫ r) ≫ l) (S.map D.β)
    exact (Homotopy.ofEq (Category.assoc _ _ _)).trans
      (hh.trans (Homotopy.ofEq (Category.comp_id _)))

set_option maxHeartbeats 800000 in
-- Normalize the scalar restriction and the two injective-resolution cocycle descriptions.
private theorem scalar_cycle (f : X ⟶ Spec (CommRingCat.of k))
    (F : SheafOfModules.{w} X.ringCatSheaf)
    (I : InjectiveResolution F) (n : ℕ)
    (c : (RingedSpace.globalSectionsComplex I).cycles n)
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ I.cocomplex.X n)
    (hφ : φ ≫ I.cocomplex.d n (n + 1) = 0)
    (hc : φ.val.app (op ⊤) (1 : Γ(X, ⊤)) =
      (RingedSpace.globalSectionsComplex I).iCycles n c) :
    letI := scalar_injective f
    letI : (RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive :=
      RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
    scalarCohomologyExtEquiv f F n
        ((I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv
          ((RingedSpace.globalSectionsComplex I).homologyπ n c)) =
      (mapResolution (scalarFunctor f) I).extMk
        (scalarUnitMorphism f ≫ (scalarFunctor f).map φ) (n + 1) rfl (by
          change (scalarUnitMorphism f ≫ (scalarFunctor f).map φ) ≫
            (scalarFunctor f).map (I.cocomplex.d n (n + 1)) = 0
          rw [Category.assoc, ← Functor.map_comp, hφ, Functor.map_zero, comp_zero]) := by
  have := scalar_injective f
  have : (RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive :=
    RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  unfold scalarCohomologyExtEquiv scalarCohomologyExtMap scalarExtMap
  have : HasExt.{w} (SheafOfModules.{w} X.ringCatSheaf) :=
    hasExt_of_enoughInjectives.{w, w, w + 1} (SheafOfModules.{w} X.ringCatSheaf)
  change (Abelian.Ext.mk₀ (scalarUnitMorphism f)).comp
    (Abelian.Ext.mapExactFunctor.{w, w + 1} (scalarFunctor f) (moduleExtEquiv F n
      ((I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv
        ((RingedSpace.globalSectionsComplex I).homologyπ n c)))) (zero_add n) = _
  have hm : moduleExtEquiv F n
      ((I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv
        ((RingedSpace.globalSectionsComplex I).homologyπ n c)) = I.extMk φ (n + 1) rfl hφ := by
    unfold moduleExtEquiv
    exact Classical.choose_spec (exists_moduleExtEquiv F n) I c φ hφ hc
  rw [hm]
  have he := extMk_map.{w, w, w + 1, w + 1, w, w + 1} (scalarFunctor f) (scalarUnitMorphism f) I
    (mapResolution (scalarFunctor f) I) (𝟙 _) (𝟙 _) (by
      rw [mapResolution_zero]; erw [Category.comp_id]) n φ hφ
  simp only [HomologicalComplex.id_f, Abelian.Ext.comp_mk₀_id] at he
  refine he.trans ?_
  congr 1

private theorem scalar_representative (f : X ⟶ Spec (CommRingCat.of k))
    (F : SheafOfModules.{w} X.ringCatSheaf) (I : InjectiveResolution F) (n : ℕ)
    (x : scalarCohomology f F n) :
    ∃ (b : SheafOfModules.unit X.ringCatSheaf ⟶ I.cocomplex.X n)
      (_hb : b ≫ I.cocomplex.d n (n + 1) = 0)
      (c : (RingedSpace.globalSectionsComplex I).cycles n),
      b.val.app (op ⊤) (1 : Γ(X, ⊤)) =
        (RingedSpace.globalSectionsComplex I).iCycles n c ∧
      (I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv
        ((RingedSpace.globalSectionsComplex I).homologyπ n c) = x := by
  obtain ⟨b, hb, he⟩ := I.extMk_surjective (moduleExtEquiv F n x) (n + 1) rfl
  let K := RingedSpace.globalSectionsComplex I
  let z := b.val.app (op ⊤) (1 : Γ(X, ⊤))
  have hz : K.d n (n + 1) z = 0 :=
    congrArg (fun t ↦ t.val.app (op ⊤) (1 : Γ(X, ⊤))) hb
  let c := K.cyclesMk z (n + 1) (by simp) hz
  have hc : b.val.app (op ⊤) (1 : Γ(X, ⊤)) = K.iCycles n c :=
    (K.i_cyclesMk z (n + 1) (by simp) hz).symm
  refine ⟨b, hb, c, hc, ?_⟩
  apply (moduleExtEquiv F n).injective
  refine Eq.trans ?_ he
  unfold moduleExtEquiv
  exact Classical.choose_spec (exists_moduleExtEquiv F n) I c b hb hc

-- Compare resolution classes before and after forgetting their module structure.
private def forgetCycle {R : Type w} [Ring R]
    (K : CochainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) (c : K.cycles n) :
    (((forget₂ _ AddCommGrpCat.{w}).mapHomologicalComplex (.up ℕ)).obj K).cycles n :=
  ((K.sc n).mapCyclesIso (forget₂ _ AddCommGrpCat.{w})).inv c

private theorem forgetCycle_i {R : Type w} [Ring R]
    (K : CochainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) (c : K.cycles n) :
    ((((forget₂ _ AddCommGrpCat.{w}).mapHomologicalComplex (.up ℕ)).obj K).iCycles n)
      (forgetCycle K n c) = K.iCycles n c := by
  have hh := (K.sc n).mapCyclesIso_hom_iCycles (forget₂ _ AddCommGrpCat.{w})
  have hh' := congrArg (fun b ↦
    ((K.sc n).mapCyclesIso (forget₂ _ AddCommGrpCat.{w})).inv ≫ b) hh
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at hh'
  exact (ConcreteCategory.congr_hom hh' c).symm

private theorem forgetCycle_π {R : Type w} [Ring R]
    (K : CochainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) (c : K.cycles n) :
    ((((forget₂ _ AddCommGrpCat.{w}).mapHomologicalComplex (.up ℕ)).obj K).homologyπ n)
      (forgetCycle K n c) =
      ((K.sc n).mapHomologyIso (forget₂ _ AddCommGrpCat.{w})).inv (K.homologyπ n c) := by
  let F := forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}
  let S := K.sc n
  have hh : (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ =
      F.map S.homologyπ ≫ (S.mapHomologyIso F).inv := by
    rw [← cancel_mono (S.mapHomologyIso F).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [S.leftHomologyData.mapHomologyIso_eq F]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    erw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
    change (S.leftHomologyData.map F).cyclesIso.inv ≫
      (S.leftHomologyData.map F).cyclesIso.hom ≫
        F.map S.leftHomologyData.π ≫ F.map S.leftHomologyData.homologyIso.inv = _
    rw [Iso.inv_hom_id_assoc, ← F.map_comp]
    have hπ := S.leftHomologyData.π_comp_homologyIso_inv
    simpa only [ShortComplex.LeftHomologyData.cyclesIso,
      ShortComplex.cyclesMapIso', Iso.refl_inv, ShortComplex.cyclesMap'_id,
      Category.id_comp] using congrArg F.map hπ
  exact (ConcreteCategory.congr_hom hh c)

private theorem forgetCycle_map {R S : Type w} [Ring R] [Ring S]
    (K : CochainComplex (ModuleCat.{w} R) ℕ)
    (L : CochainComplex (ModuleCat.{w} S) ℕ)
    (t : ((forget₂ _ AddCommGrpCat.{w}).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((forget₂ _ AddCommGrpCat.{w}).mapHomologicalComplex (.up ℕ)).obj L)
    (n : ℕ) (c : K.cycles n) (c' : L.cycles n)
    (h : t.f n (K.iCycles n c) = L.iCycles n c') :
    HomologicalComplex.cyclesMap t n (forgetCycle K n c) = forgetCycle L n c' := by
  apply (AddCommGrpCat.mono_iff_injective
    ((((forget₂ _ AddCommGrpCat.{w}).mapHomologicalComplex (.up ℕ)).obj L).iCycles n)).mp
      inferInstance
  have hh := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i t n)
    (forgetCycle K n c)
  simp only [ConcreteCategory.comp_apply, forgetCycle_i] at hh
  rw [hh, forgetCycle_i]
  exact h

set_option maxHeartbeats 800000 in
-- Forgetful homology comparisons require normalizing evaluation of module resolutions.
private theorem choices_class
    (a : Y ⟶ X) {F : SheafOfModules.{w} X.ringCatSheaf}
    {G : SheafOfModules.{w} Y.ringCatSheaf} {η : F ⟶ (pushforward a).obj G}
    (D : ModuleCohomologyFMapData a F G η) (n : ℕ)
    (c : (RingedSpace.globalSectionsComplex D.J).cycles n)
    (c' : (RingedSpace.globalSectionsComplex D.I).cycles n)
    (t : ((moduleSections X).mapHomologicalComplex (.up ℕ)).obj D.J.cocomplex ⟶
      ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj D.I.cocomplex)
    (H : Homotopy
      (t ≫ ((moduleSections X).mapHomologicalComplex (.up ℕ)).map D.lambda)
      (((moduleSections X).mapHomologicalComplex (.up ℕ)).map D.β))
    (ht : HomologicalComplex.cyclesMap t n
      (forgetCycle (RingedSpace.globalSectionsComplex D.J) n c) =
        forgetCycle (RingedSpace.globalSectionsComplex D.I) n c') :
    D.map n
      ((D.J.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv
        ((RingedSpace.globalSectionsComplex D.J).homologyπ n c)) =
      (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor Y.toRingedSpace) n).inv
        ((RingedSpace.globalSectionsComplex D.I).homologyπ n c') := by
  have ha := D.a.inv_hom_id
  rw [choices_sections_identity, Category.id_comp] at ha
  let T := HomologicalComplex.homologyFunctor AddCommGrpCat.{w} (.up ℕ) n
  have hH : T.map t ≫
      T.map (((moduleSections X).mapHomologicalComplex (.up ℕ)).map D.lambda) =
        T.map (((moduleSections X).mapHomologicalComplex (.up ℕ)).map D.β) := by
    change HomologicalComplex.homologyMap t n ≫
      HomologicalComplex.homologyMap _ n = HomologicalComplex.homologyMap _ n
    exact (HomologicalComplex.homologyMap_comp _ _ n).symm.trans (H.homologyMap_eq n)
  have hπ : T.map t
      ((((RingedSpace.globalSectionsComplex D.J).sc n).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{w})).inv
          ((RingedSpace.globalSectionsComplex D.J).homologyπ n c)) =
      (((RingedSpace.globalSectionsComplex D.I).sc n).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{w})).inv
          ((RingedSpace.globalSectionsComplex D.I).homologyπ n c') := by
    erw [← forgetCycle_π (RingedSpace.globalSectionsComplex D.J) n c,
      ← forgetCycle_π (RingedSpace.globalSectionsComplex D.I) n c']
    have hh := ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_naturality t n)
        (forgetCycle (RingedSpace.globalSectionsComplex D.J) n c)
    simpa only [ConcreteCategory.comp_apply, ht] using! hh
  unfold ModuleCohomologyFMapData.map
  simp only [ConcreteCategory.comp_apply]
  change (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor Y.toRingedSpace) n).inv
    ((((RingedSpace.globalSectionsComplex D.I).sc n).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{w})).hom
        ((inv (I := D.invertible n) (T.map (D.a.hom ≫
          ((moduleSections X).mapHomologicalComplex (.up ℕ)).map D.lambda)))
          (T.map (((moduleSections X).mapHomologicalComplex (.up ℕ)).map D.β)
            ((((RingedSpace.globalSectionsComplex D.J).sc n).mapHomologyIso
              (forget₂ _ AddCommGrpCat.{w})).inv
              ((D.J.isoRightDerivedObj
                (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).hom
                ((D.J.isoRightDerivedObj
                  (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv
                  ((RingedSpace.globalSectionsComplex D.J).homologyπ n c))))))) = _
  rw [Iso.inv_hom_id_apply]
  apply congrArg
    (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor Y.toRingedSpace) n).inv
  refine Eq.trans ?_
    (Iso.inv_hom_id_apply
      (((RingedSpace.globalSectionsComplex D.I).sc n).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{w}))
      ((RingedSpace.globalSectionsComplex D.I).homologyπ n c'))
  apply congrArg (((RingedSpace.globalSectionsComplex D.I).sc n).mapHomologyIso
    (forget₂ _ AddCommGrpCat.{w})).hom
  have : IsIso (T.map (D.a.hom ≫
      ((moduleSections X).mapHomologicalComplex (.up ℕ)).map D.lambda)) := D.invertible n
  apply (ConcreteCategory.bijective_of_isIso (T.map (D.a.hom ≫
    ((moduleSections X).mapHomologicalComplex (.up ℕ)).map D.lambda))).injective
  rw [IsIso.inv_hom_id_apply]
  erw [ha, Category.id_comp]
  rw [← hπ, ← ConcreteCategory.comp_apply, hH]

private theorem mapped_closed
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (L : C ⥤ D) [L.Additive] {K : CochainComplex C ℕ} {I : CochainComplex D ℕ}
    (γ : (L.mapHomologicalComplex (.up ℕ)).obj K ⟶ I)
    {A : C} {A' : D} (α : A' ⟶ L.obj A) (n : ℕ) (b : A ⟶ K.X n)
    (hb : b ≫ K.d n (n + 1) = 0) :
    (α ≫ L.map b ≫ γ.f n) ≫ I.d n (n + 1) = 0 := by
  rw [Category.assoc, Category.assoc, γ.comm]
  erw [← L.map_comp_assoc, hb, L.map_zero, zero_comp, comp_zero]

private theorem adj_complex_augmentation
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] (adj : L ⊣ R)
    {K : CochainComplex C ℕ} {I : CochainComplex D ℕ}
    (b : K ⟶ (R.mapHomologicalComplex (.up ℕ)).obj I)
    {F : C} {G : D} (i : F ⟶ K.X 0) (j : G ⟶ I.X 0) (v : L.obj F ⟶ G)
    (hi : i ≫ b.f 0 = adj.homEquiv _ _ v ≫ R.map j) :
    L.map i ≫ (adj_complex adj b).f 0 = v ≫ j := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    adj_complex_app]
  exact hi

set_option maxHeartbeats 800000 in
-- Normalize the two chosen resolutions and their concrete cocycles.
/-- Scalar and ordinary module pullback have the same underlying cohomology class.
Source: Stacks Project, Cohomology, Tag 01F7, functoriality and independence of lifts.
(blueprint: lem-sc-scalar-module-cohomology-pullback-comparison).

Proof: Choose injective module resolutions and the pushforward comparison used in
moduleCohomologyFMap. Evaluation at 1 identifies module morphisms from the structure
module with sections, so moduleExtEquiv sends a section cycle to its unit morphism.
Exact scalar restriction preserves the underlying cycle and its differential;
precomposition by scalarUnitMorphism is evaluation of the same morphism at 1.
The scalar pullback coefficient is adjoint to the tensor-pullback adjunction unit.
Consequently inverse image on scalar Ext followed by that coefficient is represented
by the same resolution diagram as moduleCohomologyFMap of the unit: the horizontal
map is its lift and the vertical pushforward comparison is inverted on cohomology.
Evaluation at 1 commutes with these maps. Independence of lifts and homotopies
identifies the maps for the choices recorded in the definitions. Transporting back
by scalarCohomologyExtEquiv proves equality on their common underlying carrier.
The argument holds in every natural degree, without quasi-coherence or flatness;
in degree zero it is the adjunction-unit section map. Empty schemes and zero
coefficients give zero classes. -/
theorem scalar_moduleCohomologyPullback_comparison
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (a : Y ⟶ X) (h : a ≫ f = g) (F : X.Modules) (n : ℕ)
    (x : scalarCohomology f F n) :
    scalarCohomologyPullback f g a h F n x = moduleCohomologyPullback a F n x := by
  have := scalar_injective f
  have := scalar_injective g
  let η := (Classical.choose (exists_tensorPullbackAdjunction a)).unit.app F
  let D : ModuleCohomologyFMapData a F ((tensorPullback a).obj F) η :=
    Classical.choice (moduleCohomologyFMapData_nonempty a F ((tensorPullback a).obj F) η)
  obtain ⟨b, hb, c, hc, hx⟩ := scalar_representative f F D.J n x
  obtain ⟨τ, hτ, ⟨Hτ⟩⟩ := scalar_comparison f g a h F D
  let γ := adj_complex (scalarAdj (k := k) a) τ
  have hγ : (scalarInverseImage a).map ((mapResolution (scalarFunctor f) D.J).ι.f 0) ≫
      γ.f 0 = scalarPullbackCoefficient f g a h F ≫
        (mapResolution (scalarFunctor g) D.I).ι.f 0 := by
    rw [mapResolution_zero, mapResolution_zero]
    exact adj_complex_augmentation (scalarAdj a) τ
      ((scalarFunctor f).map (D.J.ι.f 0)) ((scalarFunctor g).map (D.I.ι.f 0))
      (scalarPullbackCoefficient f g a h F) hτ
  let bS := scalarUnitMorphism f ≫ (scalarFunctor f).map b
  have hbS : bS ≫ (mapResolution (scalarFunctor f) D.J).cocomplex.d n (n + 1) = 0 := by
    change (scalarUnitMorphism f ≫ (scalarFunctor f).map b) ≫
      (scalarFunctor f).map (D.J.cocomplex.d n (n + 1)) = 0
    rw [Category.assoc, ← Functor.map_comp, hb, Functor.map_zero, comp_zero]
  let θ := (scalarInverseUnitIso a).inv ≫ (scalarInverseImage a).map bS ≫ γ.f n
  have hθ : θ ≫ (scalarFunctor g).map (D.I.cocomplex.d n (n + 1)) = 0 :=
    mapped_closed (scalarInverseImage a) γ (scalarInverseUnitIso a).inv n bS hbS
  let b' := (scalarUnitHomEquiv g (D.I.cocomplex.X n)).symm θ
  have hb' : b' ≫ D.I.cocomplex.d n (n + 1) = 0 :=
    scalarUnitHomEquiv_closed g _ θ hθ
  let K := RingedSpace.globalSectionsComplex D.I
  let z := b'.val.app (op ⊤) (1 : Γ(Y, ⊤))
  have hz : K.d n (n + 1) z = 0 :=
    congrArg (fun t ↦ t.val.app (op ⊤) (1 : Γ(Y, ⊤))) hb'
  let c' := K.cyclesMk z (n + 1) (by simp) hz
  have hc' : b'.val.app (op ⊤) (1 : Γ(Y, ⊤)) = K.iCycles n c' :=
    (K.i_cyclesMk z (n + 1) (by simp) hz).symm
  have he : scalarCohomologyExtEquiv f F n x =
      (mapResolution (scalarFunctor f) D.J).extMk bS (n + 1) rfl hbS := by
    rw [← hx]
    exact scalar_cycle f F D.J n c b hb hc
  have hp := extMk_map.{w, w, w + 1, w + 1, w + 1, w + 1}
    (scalarInverseImage a) (scalarInverseUnitIso a).inv
    (mapResolution (scalarFunctor f) D.J) (mapResolution (scalarFunctor g) D.I)
    (scalarPullbackCoefficient f g a h F) γ hγ n bS hbS
  have he' := scalar_cycle g ((tensorPullback a).obj F) D.I n c' b' hb' hc'
  have hθ' : scalarUnitMorphism g ≫ (scalarFunctor g).map b' = θ :=
    (scalarUnitHomEquiv g (D.I.cocomplex.X n)).apply_symm_apply θ
  have hclass : D.map n x =
      (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor Y.toRingedSpace) n).inv
        (K.homologyπ n c') := by
    let t : ((moduleSections X).mapHomologicalComplex (.up ℕ)).obj D.J.cocomplex ⟶
        ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj D.I.cocomplex :=
      ((scalarSections X k).mapHomologicalComplex (.up ℕ)).map τ
    have HH : Homotopy
        (t ≫ ((moduleSections X).mapHomologicalComplex (.up ℕ)).map D.lambda)
        (((moduleSections X).mapHomologicalComplex (.up ℕ)).map D.β) := by
      have HH := (scalarSections X k).mapHomotopy Hτ
      convert HH using 1 <;> rfl
    have ht : HomologicalComplex.cyclesMap t n
        (forgetCycle (RingedSpace.globalSectionsComplex D.J) n c) =
          forgetCycle K n c' := by
      apply forgetCycle_map (RingedSpace.globalSectionsComplex D.J) K t n c c'
      rw [← hc, ← hc']
      have hs := scalarSection_pullback a bS (γ.f n)
      have hγn := adj_complex_app (scalarAdj (k := k) a) τ n
      change (scalarAdj (k := k) a).homEquiv _ _ (γ.f n) = τ.f n at hγn
      change scalarSection (scalarSheaf g (D.I.cocomplex.X n)) θ =
        ((scalarAdj (k := k) a).homEquiv _ _ (γ.f n)).hom.app (op ⊤)
          (scalarSection (scalarSheaf f (D.J.cocomplex.X n)) bS) at hs
      rw [hγn] at hs
      have hz' : b'.val.app (op ⊤) (1 : Γ(Y, ⊤)) =
          scalarSection (scalarSheaf g (D.I.cocomplex.X n)) θ := by
        change moduleSectionEquiv _ ((moduleSectionEquiv _).symm _) = _
        exact (moduleSectionEquiv _).apply_symm_apply _
      rw [hz', hs]
      have hbs : scalarSection (scalarSheaf f (D.J.cocomplex.X n)) bS =
          b.val.app (op ⊤) (1 : Γ(X, ⊤)) := scalarSection_module f b
      rw [hbs]
      rfl
    rw [← hx]
    exact choices_class a D n c c' t HH ht
  apply (scalarCohomologyExtEquiv g ((tensorPullback a).obj F) n).injective
  unfold scalarCohomologyPullback
  rw [AddEquiv.apply_symm_apply, he]
  change _ = scalarCohomologyExtEquiv g ((tensorPullback a).obj F) n (D.map n x)
  rw [hclass, he']
  refine hp.trans ?_
  congr 1
  exact hθ'.symm

end
end AlgebraicGeometry.Scheme.Modules
