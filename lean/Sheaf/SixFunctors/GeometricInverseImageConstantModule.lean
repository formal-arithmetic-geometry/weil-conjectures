/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
public import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
import Mathlib.Algebra.Category.Grp.LeftExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Geometric inverse image preserves constant module sheaves

Source: Stacks Project, `sites.tex`, Tags 0H7J and 00YV
(blueprint: lem-sfb-geometric-inverse-image-constant-module).

The constant module sheaf is represented by `siteConstantModuleFunctorGeneral`. The
recorded geometric-morphism lift supplies the module inverse image and its underlying
set comparison; the theorem states the resulting canonical constant-module
isomorphisms and their naturality in the coefficient module.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private def pointCofan (E : Type u) : Cofan (fun _ : E ↦ PUnit.{u + 1}) :=
  Cofan.mk E (fun e ↦ TypeCat.ofHom (fun _ ↦ e))

private def pointCofanIsColimit (E : Type u) : IsColimit (pointCofan E) :=
  Cofan.IsColimit.mk _ (fun s ↦ TypeCat.ofHom (fun e ↦ s.inj e PUnit.unit))
    (by intros; ext x; cases x; rfl)
    (by intro s f h; ext e; exact ConcreteCategory.congr_hom (h e) PUnit.unit)

private def mapPointCofanIsColimit {A : Type*} [Category A]
    (F : Type u ⥤ A) [PreservesColimitsOfSize.{u, u} F] (E : Type u) :
    IsColimit (Cofan.mk (F.obj E)
      (fun e : E ↦ F.map (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ e)))) :=
  isColimitCofanMkObjOfIsColimit F _ _ (pointCofanIsColimit E)

private def pointComparisonHom {A : Type*} [Category A]
    (F G : Type u ⥤ A) [PreservesColimitsOfSize.{u, u} F]
    (p : F.obj PUnit.{u + 1} ⟶ G.obj PUnit.{u + 1}) (E : Type u) : F.obj E ⟶ G.obj E :=
  (mapPointCofanIsColimit F E).desc (Cofan.mk (G.obj E)
    (fun e ↦ p ≫ G.map (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ e))))

private theorem pointComparisonHom_fac {A : Type*} [Category A]
    (F G : Type u ⥤ A) [PreservesColimitsOfSize.{u, u} F]
    (p : F.obj PUnit.{u + 1} ⟶ G.obj PUnit.{u + 1}) (E : Type u) (e : E) :
    F.map (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ e)) ≫ pointComparisonHom F G p E =
      p ≫ G.map (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ e)) :=
  (mapPointCofanIsColimit F E).fac _ (Discrete.mk e)

private def pointComparison {A : Type*} [Category A]
    (F G : Type u ⥤ A) [PreservesColimitsOfSize.{u, u} F]
    [PreservesColimitsOfSize.{u, u} G] (p : F.obj PUnit.{u + 1} ≅ G.obj PUnit.{u + 1})
    (E : Type u) : F.obj E ≅ G.obj E where
  hom := pointComparisonHom F G p.hom E
  inv := pointComparisonHom G F p.inv E
  hom_inv_id := by
    apply Cofan.IsColimit.hom_ext (mapPointCofanIsColimit F E)
    intro e
    dsimp
    rw [← Category.assoc, pointComparisonHom_fac, Category.assoc, pointComparisonHom_fac]
    simp
  inv_hom_id := by
    apply Cofan.IsColimit.hom_ext (mapPointCofanIsColimit G E)
    intro e
    dsimp
    rw [← Category.assoc, pointComparisonHom_fac, Category.assoc, pointComparisonHom_fac]
    simp

private def pointComparisonNatIso {A : Type*} [Category A]
    (F G : Type u ⥤ A) [PreservesColimitsOfSize.{u, u} F]
    [PreservesColimitsOfSize.{u, u} G] (p : F.obj PUnit.{u + 1} ≅ G.obj PUnit.{u + 1}) :
    F ≅ G :=
  NatIso.ofComponents (pointComparison F G p) (by
    intro E E' f
    apply Cofan.IsColimit.hom_ext (mapPointCofanIsColimit F E)
    intro e
    dsimp [pointComparison]
    rw [← Category.assoc, ← F.map_comp]
    change F.map (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ f e)) ≫ _ = _
    rw [pointComparisonHom_fac, ← Category.assoc, pointComparisonHom_fac,
      Category.assoc, ← G.map_comp]
    rfl)

private def naturalAdditiveMap
    (R : Type u) [CommRing R] (F G : ModuleCat.{u} R ⥤ AddCommGrpCat.{u})
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (n : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat) : F ⟶ G := by
  let E := AddCommGrpCat.leftExactFunctorForgetEquivalence (ModuleCat.{u} R)
  let n' : E.functor.obj (LeftExactFunctor.of F) ⟶
      E.functor.obj (LeftExactFunctor.of G) := ObjectProperty.homMk n
  exact (E.functor.preimage n').hom

private theorem naturalAdditiveMap_forget
    (R : Type u) [CommRing R] (F G : ModuleCat.{u} R ⥤ AddCommGrpCat.{u})
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (n : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat) :
    Functor.whiskerRight (naturalAdditiveMap R F G n) (forget AddCommGrpCat) = n := by
  let E := AddCommGrpCat.leftExactFunctorForgetEquivalence (ModuleCat.{u} R)
  let n' : E.functor.obj (LeftExactFunctor.of F) ⟶
      E.functor.obj (LeftExactFunctor.of G) := ObjectProperty.homMk n
  exact congrArg (fun f ↦ f.hom) (E.functor.map_preimage n')

private def abelianLiftSetNatTrans
    {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)
    (R : Type u) [CommRing R]
    (F G : ModuleCat.{u} R ⥤ Sheaf K AddCommGrpCat.{u})
    [∀ U : Dᵒᵖ, PreservesFiniteLimits (F ⋙ (sheafSections K AddCommGrpCat).obj U)]
    [∀ U : Dᵒᵖ, PreservesFiniteLimits (G ⋙ (sheafSections K AddCommGrpCat).obj U)]
    (n : F ⋙ ConstantLeftModuleInverseImage.U K ⟶
      G ⋙ ConstantLeftModuleInverseImage.U K) : F ⟶ G := by
  let a (U : Dᵒᵖ) := naturalAdditiveMap R
    (F ⋙ (sheafSections K AddCommGrpCat).obj U)
    (G ⋙ (sheafSections K AddCommGrpCat).obj U)
    (Functor.whiskerRight n ((sheafSections K (Type u)).obj U))
  have ha (U : Dᵒᵖ) (M : ModuleCat.{u} R) :
      (forget AddCommGrpCat).map ((a U).app M) = (n.app M).hom.app U := by
    exact congrArg (fun t ↦ t.app M) (naturalAdditiveMap_forget R
      (F ⋙ (sheafSections K AddCommGrpCat).obj U)
      (G ⋙ (sheafSections K AddCommGrpCat).obj U)
      (Functor.whiskerRight n ((sheafSections K (Type u)).obj U)))
  refine
    { app := fun M ↦
        { hom :=
            { app := fun U ↦ (a U).app M
              naturality := ?_ } }
      naturality := ?_ }
  · rename_i M
    intro U V f
    apply (forget AddCommGrpCat).map_injective
    change (forget AddCommGrpCat).map ((F.obj M).obj.map f) ≫
        (forget AddCommGrpCat).map ((a V).app M) =
      (forget AddCommGrpCat).map ((a U).app M) ≫
        (forget AddCommGrpCat).map ((G.obj M).obj.map f)
    rw [ha, ha]
    exact (n.app M).hom.naturality f
  · intro M N f
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply (forget AddCommGrpCat).map_injective
    change (forget AddCommGrpCat).map ((F.map f).hom.app U) ≫
        (forget AddCommGrpCat).map ((a U).app N) =
      (forget AddCommGrpCat).map ((a U).app M) ≫
        (forget AddCommGrpCat).map ((G.map f).hom.app U)
    rw [ha, ha]
    exact congrArg (fun t ↦ t.hom.app U) (n.naturality f)

private theorem abelianLiftSetNatTrans_forget
    {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)
    (R : Type u) [CommRing R]
    (F G : ModuleCat.{u} R ⥤ Sheaf K AddCommGrpCat.{u})
    [∀ U : Dᵒᵖ, PreservesFiniteLimits (F ⋙ (sheafSections K AddCommGrpCat).obj U)]
    [∀ U : Dᵒᵖ, PreservesFiniteLimits (G ⋙ (sheafSections K AddCommGrpCat).obj U)]
    (n : F ⋙ ConstantLeftModuleInverseImage.U K ⟶
      G ⋙ ConstantLeftModuleInverseImage.U K) :
    Functor.whiskerRight (abelianLiftSetNatTrans K R F G n)
      (ConstantLeftModuleInverseImage.U K) = n := by
  apply NatTrans.ext
  funext M
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact congrArg (fun t ↦ t.app M) (naturalAdditiveMap_forget R
      (F ⋙ (sheafSections K AddCommGrpCat).obj U)
      (G ⋙ (sheafSections K AddCommGrpCat).obj U)
      (Functor.whiskerRight n ((sheafSections K (Type u)).obj U)))

private def moduleScalar
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Type u) [CommRing R] [HasWeakSheafify J RingCat.{u}]
    (M : ConstantLeftModuleInverseImage.Modules J R) (r : R) :
    (ConstantLeftModuleInverseImage.V J R).obj M ⟶
      (ConstantLeftModuleInverseImage.V J R).obj M where
  hom :=
    { app := fun T ↦ (M.val.obj T).smul
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app T r)
      naturality := fun {T T'} f ↦ by
        apply AddCommGrpCat.ext
        intro x
        change M.val.obj T at x
        symm
        change M.val.map f
          (((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app T r) • x) =
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app T' r) • M.val.map f x
        rw [M.val.map_smul]
        congr 1
        exact CategoryTheory.congr_fun
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).naturality f) r |>.symm }

private theorem moduleScalar_isScalar
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Type u) [CommRing R] [HasWeakSheafify J RingCat.{u}]
    (M : ConstantLeftModuleInverseImage.Modules J R) (r : R) :
    ConstantLeftModuleInverseImage.IsScalar J R M r (moduleScalar J R M r) := by
  intro T x
  rfl

private def constantScalar (R : Type u) [CommRing R] (M : ModuleCat.{u} R) (r : R) :
    M ⟶ M := ModuleCat.ofHom (LinearMap.lsmul R M r)

set_option backward.isDefEq.respectTransparency false in
private def linearSheafHom
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Type u) [CommRing R] [HasWeakSheafify J RingCat.{u}]
    (M N : ConstantLeftModuleInverseImage.Modules J R)
    (a : (ConstantLeftModuleInverseImage.V J R).obj M ⟶
      (ConstantLeftModuleInverseImage.V J R).obj N)
    (ha : ∀ r : R, moduleScalar J R M r ≫ a = a ≫ moduleScalar J R N r) : M ⟶ N := by
  let α := toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))
  let b : (PresheafOfModules.restrictScalars α).obj M.val ⟶
      (PresheafOfModules.restrictScalars α).obj N.val :=
    PresheafOfModules.homMk a.hom (by
      intro T r x
      exact congrArg (fun f ↦ (f.hom.app T).hom x) (ha r))
  exact ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective α N.isSheaf).symm b⟩

private theorem linearSheafHom_forget
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Type u) [CommRing R] [HasWeakSheafify J RingCat.{u}]
    (M N : ConstantLeftModuleInverseImage.Modules J R)
    (a : (ConstantLeftModuleInverseImage.V J R).obj M ⟶
      (ConstantLeftModuleInverseImage.V J R).obj N)
    (ha : ∀ r : R, moduleScalar J R M r ≫ a = a ≫ moduleScalar J R N r) :
    (ConstantLeftModuleInverseImage.V J R).map (linearSheafHom J R M N a ha) = a := by
  rfl

private def linearSheafNatTrans
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Type u) [CommRing R] [HasWeakSheafify J RingCat.{u}]
    (F G : ModuleCat.{u} R ⥤ ConstantLeftModuleInverseImage.Modules J R)
    (hF : ∀ M r, (ConstantLeftModuleInverseImage.V J R).map
      (F.map (constantScalar R M r)) = moduleScalar J R (F.obj M) r)
    (hG : ∀ M r, (ConstantLeftModuleInverseImage.V J R).map
      (G.map (constantScalar R M r)) = moduleScalar J R (G.obj M) r)
    (a : F ⋙ ConstantLeftModuleInverseImage.V J R ⟶
      G ⋙ ConstantLeftModuleInverseImage.V J R) : F ⟶ G where
  app M := linearSheafHom J R _ _ (a.app M) (fun r ↦ by
    rw [← hF M r, ← hG M r]
    exact a.naturality (constantScalar R M r))
  naturality := fun {M N} f ↦ by
    apply (ConstantLeftModuleInverseImage.V J R).map_injective
    simpa only [Functor.map_comp, linearSheafHom_forget, Functor.comp_map] using a.naturality f

private theorem linearSheafNatTrans_forget
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Type u) [CommRing R] [HasWeakSheafify J RingCat.{u}]
    (F G : ModuleCat.{u} R ⥤ ConstantLeftModuleInverseImage.Modules J R)
    (hF : ∀ M r, (ConstantLeftModuleInverseImage.V J R).map
      (F.map (constantScalar R M r)) = moduleScalar J R (F.obj M) r)
    (hG : ∀ M r, (ConstantLeftModuleInverseImage.V J R).map
      (G.map (constantScalar R M r)) = moduleScalar J R (G.obj M) r)
    (a : F ⋙ ConstantLeftModuleInverseImage.V J R ⟶
      G ⋙ ConstantLeftModuleInverseImage.V J R) :
    Functor.whiskerRight (linearSheafNatTrans J R F G hF hG a)
      (ConstantLeftModuleInverseImage.V J R) = a := by
  rfl

private theorem constantScalar_map
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Type u) [CommRing R] [HasWeakSheafify J RingCat.{u}]
    (M : ModuleCat.{u} R) (r : R) :
    (ConstantLeftModuleInverseImage.V J R).map
        ((siteConstantModuleFunctorGeneral J R).map (constantScalar R M r)) =
      moduleScalar J R ((siteConstantModuleFunctorGeneral J R).obj M) r := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _
    ((ConstantLeftModuleInverseImage.V J R).obj
      ((siteConstantModuleFunctorGeneral J R).obj M)).property
  change _ ≫ sheafifyMap J _ = _
  rw [← toSheafify_naturality]
  ext T x
  exact ((PresheafOfModules.toSheafify
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))
    (toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj M).presheaf)).app
      T).hom.map_smul r x

private theorem constantModule_preservesFiniteLimits
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Type u) [CommRing R] [HasWeakSheafify J RingCat.{u}] :
    PreservesFiniteLimits (siteConstantModuleFunctorGeneral J R) := by
  have : PreservesFiniteLimits (siteConstantModuleFunctorGeneral J R ⋙
      ConstantLeftModuleInverseImage.V J R) := by
    change PreservesFiniteLimits
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⋙ constantSheaf J AddCommGrpCat.{u})
    have : PreservesFiniteLimits (presheafToSheaf J AddCommGrpCat.{u}) := inferInstance
    have : PreservesFiniteLimits (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _) := inferInstance
    have : PreservesFiniteLimits (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
      inferInstance
    have : PreservesFiniteLimits (constantSheaf J AddCommGrpCat.{u}) :=
      comp_preservesFiniteLimits (Functor.const Cᵒᵖ) (presheafToSheaf J AddCommGrpCat.{u})
    exact comp_preservesFiniteLimits _ (constantSheaf J AddCommGrpCat.{u})
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (ConstantLeftModuleInverseImage.V J R)

private theorem inverseImage_constantScalar_map
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (R : Type u) [CommRing R]
    [HasWeakSheafify J RingCat.{u}] [HasWeakSheafify K RingCat.{u}]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (Rfun : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ Rfun) (hL : PreservesFiniteLimits L)
    (d : ConstantLeftModuleInverseImageData.{u, w} J K R L Rfun adj hL)
    (M : ModuleCat.{u} R) (r : R) :
    (ConstantLeftModuleInverseImage.V K R).map
        (d.moduleFunctor.map ((siteConstantModuleFunctorGeneral J R).map
          (constantScalar R M r))) =
      moduleScalar K R (d.moduleFunctor.obj ((siteConstantModuleFunctorGeneral J R).obj M)) r := by
  apply (cancel_mono (d.underlyingIso.hom.app
    ((siteConstantModuleFunctorGeneral J R).obj M))).1
  rw [show (ConstantLeftModuleInverseImage.V K R).map
      (d.moduleFunctor.map ((siteConstantModuleFunctorGeneral J R).map
        (constantScalar R M r))) ≫ d.underlyingIso.hom.app _ = _ from
    d.underlyingIso.hom.naturality
      ((siteConstantModuleFunctorGeneral J R).map (constantScalar R M r))]
  change d.underlyingIso.hom.app _ ≫ d.abelianInverse.map
    ((ConstantLeftModuleInverseImage.V J R).map
      ((siteConstantModuleFunctorGeneral J R).map (constantScalar R M r))) = _
  rw [constantScalar_map]
  exact (d.scalar_compatibility _ r _ _ (moduleScalar_isScalar J R _ r)
    (moduleScalar_isScalar K R _ r)).symm

/-- The underlying set sheaf of the genuine constant module sheaf, identified with
set-valued constant sheafification by the canonical forgetful comparison.
Source: Stacks Project, Sites, 00YR and 0H7J; Modules on Sites, 03CY
(blueprint: lem-sfb-geometric-inverse-image-constant-module). -/
def constantModuleUnderlyingSetIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Type u) [CommRing R] [HasWeakSheafify J RingCat.{u}]
    (M : ModuleCat.{u} R) :
    (ConstantLeftModuleInverseImage.W J R).obj
        ((siteConstantModuleFunctorGeneral J R).obj M) ≅
      (constantSheaf J (Type u)).obj M :=
  (constantCommuteCompose J (forget AddCommGrpCat.{u})).app
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M)

private def constantModuleUnderlyingNatIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Type u) [CommRing R] [HasWeakSheafify J RingCat.{u}] :
    siteConstantModuleFunctorGeneral J R ⋙ ConstantLeftModuleInverseImage.W J R ≅
      forget (ModuleCat.{u} R) ⋙ constantSheaf J (Type u) :=
  Functor.isoWhiskerLeft (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    (constantCommuteCompose J (forget AddCommGrpCat.{u}))

private def constantModuleImageSetIso
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (R : Type u) [CommRing R]
    [HasWeakSheafify J RingCat.{u}] [HasWeakSheafify K RingCat.{u}]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (Rfun : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ Rfun) (hL : PreservesFiniteLimits L)
    (d : ConstantLeftModuleInverseImageData.{u, w} J K R L Rfun adj hL) :
    siteConstantModuleFunctorGeneral J R ⋙ d.moduleFunctor ⋙
        ConstantLeftModuleInverseImage.W K R ≅
      siteConstantModuleFunctorGeneral K R ⋙ ConstantLeftModuleInverseImage.W K R := by
  have : PreservesColimitsOfSize.{u, u} L := adj.leftAdjoint_preservesColimits
  have (H : GrothendieckTopology C) :
      PreservesColimitsOfSize.{u, u} (constantSheaf H (Type u)) := by
    dsimp [constantSheaf]
    infer_instance
  have : PreservesColimitsOfSize.{u, u} (constantSheaf K (Type u)) := by
    dsimp [constantSheaf]
    infer_instance
  let c := pointComparisonNatIso (constantSheaf J (Type u) ⋙ L)
    (constantSheaf K (Type u)) d.pointIso
  exact Functor.isoWhiskerLeft (siteConstantModuleFunctorGeneral J R) d.moduleSetIso ≪≫
    Functor.isoWhiskerRight (constantModuleUnderlyingNatIso J R) L ≪≫
    Functor.isoWhiskerLeft (forget (ModuleCat.{u} R)) c ≪≫ (constantModuleUnderlyingNatIso K R).symm

/-- The summand labelled by `m` in the underlying constant module sheaf: first take
constant set sheafification of the map from a singleton with value `m`, then use the
canonical module/set sheafification comparison.
Source: Stacks Project, Sites, 0H7J; Modules on Sites, 03CY
(blueprint: lem-sfb-geometric-inverse-image-constant-module). -/
def constantModuleSetSection
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Type u) [CommRing R] [HasWeakSheafify J RingCat.{u}]
    (M : ModuleCat.{u} R) (m : M) :
    (constantSheaf J (Type u)).obj PUnit.{u+1} ⟶
      (ConstantLeftModuleInverseImage.W J R).obj
        ((siteConstantModuleFunctorGeneral J R).obj M) :=
  (constantSheaf J (Type u)).map (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ m)) ≫
    (constantModuleUnderlyingSetIso J R M).inv

/-- Geometric inverse image preserves genuine constant module sheaves, naturally in
all linear maps, with the underlying comparison normalized on each constant section.

Source: Stacks Project, Sites, Tags 0H7J and 00YV
(blueprint: lem-sfb-geometric-inverse-image-constant-module).

Proof (the five steps of the node):
1. By `def-weil-pbc-constant-sheaf` and `def-weil-pbc-sheafification`, maps from the
constant set sheaf of `E` to a sheaf are families of maps from the terminal sheaf,
indexed by `E`. Thus it is the coproduct of `E` terminal sheaves, including `E` empty.
Its inclusions are the constant sections, and a set map carries the labelled inclusion
to the inclusion with its image label.
2. The adjunction makes `L` preserve these coproducts, by
`lem-weil-pbc-left-adjoint-preserves-colimits`. Finite-limit preservation identifies
`L` of the terminal sheaf with the terminal sheaf. The coproduct universal property
gives the unique isomorphism preserving every labelled inclusion, naturally in set maps.
3. By `lem-weil-pbc-sheafification-sets-exact`, constant sheafification preserves
finite products. Naturality for the projections gives compatibility of the comparison
with products. The underlying module and ring sheaves are these constant set sheaves,
with their units, by `lem-cbc-module-sheafification-underlying-sets` and
`lem-pc-sites-sheafification-underlying-sets`.
4. In `lem-pe-constant-left-module-inverse-image` the lifted operations come from `L`.
Naturality for addition, zero, negation, and scalar multiplication makes the set
comparison linear; `lem-pc-sites-module-sheafification-interface` identifies the genuine
constant-module action. Its ring comparison agrees with the recorded one because both
preserve scalar inclusions. The inverse comparison is linear as well.
5. Apply set naturality to each linear map to obtain the displayed module naturality.
The last equation is precisely the labelled-inclusion characterization in step 2,
using the dependency's `moduleSetIso` to forget module inverse image and `pointIso`
to identify inverse image of the terminal sheaf. -/
theorem geometric_inverse_image_constant_module
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (R : Type u) [CommRing R]
    [HasWeakSheafify J RingCat.{u}] [HasWeakSheafify K RingCat.{u}]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (Rfun : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ Rfun) (hL : PreservesFiniteLimits L) :
    ∃ d : ConstantLeftModuleInverseImageData.{u, w} J K R L Rfun adj hL,
      ∃ e : ∀ M : ModuleCat.{u} R,
        d.moduleFunctor.obj ((siteConstantModuleFunctorGeneral J R).obj M) ≅
          (siteConstantModuleFunctorGeneral K R).obj M,
        (∀ (M N : ModuleCat.{u} R) (f : M ⟶ N),
          d.moduleFunctor.map ((siteConstantModuleFunctorGeneral J R).map f) ≫ (e N).hom =
            (e M).hom ≫ (siteConstantModuleFunctorGeneral K R).map f) ∧
        (∀ (M : ModuleCat.{u} R) (m : M),
          L.map (constantModuleSetSection J R M m) ≫
              d.moduleSetIso.inv.app ((siteConstantModuleFunctorGeneral J R).obj M) ≫
              (ConstantLeftModuleInverseImage.W K R).map (e M).hom =
            d.pointIso.hom ≫ constantModuleSetSection K R M m) := by
  obtain ⟨d⟩ := constant_left_module_inverse_image.{u, w} J K R L Rfun adj hL
  let F := siteConstantModuleFunctorGeneral J R ⋙ d.moduleFunctor
  let G := siteConstantModuleFunctorGeneral K R
  have : PreservesFiniteLimits (siteConstantModuleFunctorGeneral J R) :=
    constantModule_preservesFiniteLimits J R
  have : PreservesFiniteLimits G := constantModule_preservesFiniteLimits K R
  have : PreservesFiniteLimits d.moduleFunctor := d.preservesFiniteLimits
  have : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (F ⋙ ConstantLeftModuleInverseImage.V K R) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (G ⋙ ConstantLeftModuleInverseImage.V K R) :=
    comp_preservesFiniteLimits _ _
  have (T : Dᵒᵖ) : PreservesFiniteLimits
      ((sheafSections K AddCommGrpCat.{u}).obj T) := by
    change PreservesFiniteLimits
      (sheafToPresheaf K AddCommGrpCat.{u} ⋙
        (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T)
    infer_instance
  have (T : Dᵒᵖ) : PreservesFiniteLimits
      ((F ⋙ ConstantLeftModuleInverseImage.V K R) ⋙
        (sheafSections K AddCommGrpCat.{u}).obj T) := comp_preservesFiniteLimits _ _
  have (T : Dᵒᵖ) : PreservesFiniteLimits
      ((G ⋙ ConstantLeftModuleInverseImage.V K R) ⋙
        (sheafSections K AddCommGrpCat.{u}).obj T) := comp_preservesFiniteLimits _ _
  let c := constantModuleImageSetIso J K R L Rfun adj hL d
  let a := abelianLiftSetNatTrans K R
    (F ⋙ ConstantLeftModuleInverseImage.V K R)
    (G ⋙ ConstantLeftModuleInverseImage.V K R) c.hom
  let b := linearSheafNatTrans K R F G
    (inverseImage_constantScalar_map J K R L Rfun adj hL d)
    (constantScalar_map K R) a
  have hb : Functor.whiskerRight b (ConstantLeftModuleInverseImage.W K R) = c.hom := by
    change Functor.whiskerRight (Functor.whiskerRight b (ConstantLeftModuleInverseImage.V K R))
      (ConstantLeftModuleInverseImage.U K) = c.hom
    rw [linearSheafNatTrans_forget, abelianLiftSetNatTrans_forget]
  have (M : ModuleCat.{u} R) : IsIso (b.app M) := by
    have : IsIso ((ConstantLeftModuleInverseImage.W K R).map (b.app M)) := by
      change IsIso ((Functor.whiskerRight b (ConstantLeftModuleInverseImage.W K R)).app M)
      rw [hb]
      infer_instance
    exact isIso_of_reflects_iso _ (ConstantLeftModuleInverseImage.W K R)
  refine ⟨d, fun M ↦ asIso (b.app M), fun M N f ↦ b.naturality f, ?_⟩
  intro M m
  change L.map (constantModuleSetSection J R M m) ≫
      d.moduleSetIso.inv.app _ ≫
      (Functor.whiskerRight b (ConstantLeftModuleInverseImage.W K R)).app M = _
  rw [hb]
  have : PreservesColimitsOfSize.{u, u} L := adj.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u, u} (constantSheaf J (Type u)) := by
    dsimp [constantSheaf]
    infer_instance
  have : PreservesColimitsOfSize.{u, u} (constantSheaf K (Type u)) := by
    dsimp [constantSheaf]
    infer_instance
  dsimp [c, constantModuleImageSetIso, constantModuleSetSection,
    constantModuleUnderlyingNatIso]
  dsimp only [constantModuleUnderlyingSetIso]
  rw [L.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← L.map_comp_assoc]
  simp only [Iso.app_inv]
  erw [Iso.inv_hom_id_app]
  rw [← Category.assoc]
  change ((constantSheaf J (Type u) ⋙ L).map
      (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ m)) ≫
      pointComparisonHom (constantSheaf J (Type u) ⋙ L)
        (constantSheaf K (Type u)) d.pointIso.hom M) ≫
      (constantModuleUnderlyingSetIso K R M).inv = _
  rw [pointComparisonHom_fac]
  exact Category.assoc _ _ _

end CategoryTheory
