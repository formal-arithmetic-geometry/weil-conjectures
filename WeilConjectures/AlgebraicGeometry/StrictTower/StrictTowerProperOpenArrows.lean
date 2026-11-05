/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenBaseChangeNormalized
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange

/-!
# Normalized proper/open calculus on strict pro-etale towers

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D, 0F7F, 07A7 and 09AE, and the explicit
strict-tower refinement in the blueprint (blueprint: def-cbc-strict-tower-proper-open-arrows).

The index `n : ℕ` denotes positive level `n+1`. All derived categories below localize
complexes of strict towers, rather than forming towers in separate derived categories.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

-- The right-derived construction agrees with exact localization, without imposing
-- a monoidal structure or a flat-resolution construction on a tower category.
@[irreducible] private noncomputable def exactAdj
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R) :
    L.mapDerivedCategory ⊣ R.mapDerivedCategory :=
  a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    R.rightDerivedFunctorIsoMapDerivedCategory

-- Exact localization preserves mate equations for the specified unit normalization.
section ExactMates

variable {C₁ D₁ C₂ D₂ : Type*} [Category C₁] [Category D₁] [Category C₂] [Category D₂]
  [Abelian C₁] [Abelian D₁] [Abelian C₂] [Abelian D₂]
  [HasDerivedCategory C₁] [HasDerivedCategory D₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₂]
  {f₁ : C₁ ⥤ D₁} {g₁ : D₁ ⥤ C₁} (adj₁ : f₁ ⊣ g₁)
  {f₂ : C₂ ⥤ D₂} {g₂ : D₂ ⥤ C₂} (adj₂ : f₂ ⊣ g₂)
  {u : C₁ ⥤ C₂} {v : D₁ ⥤ D₂}
  [f₁.Additive] [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
  [g₁.Additive] [PreservesFiniteLimits g₁] [PreservesFiniteColimits g₁]
  [f₂.Additive] [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂]
  [g₂.Additive] [PreservesFiniteLimits g₂] [PreservesFiniteColimits g₂]
  [u.Additive] [PreservesFiniteLimits u] [PreservesFiniteColimits u]
  [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
  (τ : g₁ ⋙ u ≅ v ⋙ g₂) (β : u ⋙ f₂ ≅ f₁ ⋙ v)
  (d₁ : f₁.mapDerivedCategory ⊣ g₁.mapDerivedCategory)
  (d₂ : f₂.mapDerivedCategory ⊣ g₂.mapDerivedCategory)
  (hu₁ : ∀ X : HomotopyCategory C₁ (.up ℤ),
    d₁.unit.app (DerivedCategory.Qh.obj X) ≫
        g₁.mapDerivedCategory.map (f₁.mapDerivedCategoryFactorsh.hom.app X) ≫
        g₁.mapDerivedCategoryFactorsh.hom.app ((f₁.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X))
  (hu₂ : ∀ X : HomotopyCategory C₂ (.up ℤ),
    d₂.unit.app (DerivedCategory.Qh.obj X) ≫
        g₂.mapDerivedCategory.map (f₂.mapDerivedCategoryFactorsh.hom.app X) ≫
        g₂.mapDerivedCategoryFactorsh.hom.app ((f₂.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).unit.app X))

end ExactMates

section EvaluationCoherence

private abbrev W {C D : Type*} [Category C] [Category D] (F : C ⥤ D) :=
  (Functor.whiskeringRight ℕᵒᵖ C D).obj F

private instance W_limits {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteLimits F] : PreservesFiniteLimits (W F) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

private instance W_colimits {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteColimits F] : PreservesFiniteColimits (W F) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

variable {C D H : Type*} [Category C] [Category D] [Category H]
  [Abelian C] [Abelian D] [Abelian H]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory H]
  [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
  [HasDerivedCategory (ℕᵒᵖ ⥤ H)]
  (F G : C ⥤ D) (K : D ⥤ H)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]

@[irreducible] private noncomputable def towerSquare
    {C A A' D : Type*} [Category C] [Category A] [Category A'] [Category D]
    (F₁ : C ⥤ A) (F₂ : A ⥤ D) (G₁ : C ⥤ A') (G₂ : A' ⥤ D)
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) : W F₁ ⋙ W F₂ ≅ W G₁ ⋙ W G₂ :=
  Functor.whiskeringRightObjCompIso F₁ F₂ ≪≫
    (Functor.whiskeringRight ℕᵒᵖ C D).mapIso e ≪≫
    (Functor.whiskeringRightObjCompIso G₁ G₂).symm

end EvaluationCoherence

private theorem unit_iso_of_comparison
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    (E : C ⥤ C') (S : D ⥤ D') (T : C' ⥤ D')
    [E.Full] [E.Faithful] [S.Faithful] [T.Full] [T.Faithful]
    (e : L ⋙ S ≅ E ⋙ T) : IsIso a.unit := by
  have : (L ⋙ S).Full := Functor.Full.of_iso e.symm
  have : (L ⋙ S).Faithful := Functor.Faithful.of_iso e.symm
  have : L.Full := Functor.Full.of_comp_faithful L S
  have : L.Faithful := Functor.Faithful.of_comp L S
  infer_instance

private theorem tower_unit_iso
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) [IsIso a.unit] : IsIso (a.whiskerRight ℕᵒᵖ).unit := by
  have ht (M) : IsIso ((a.whiskerRight ℕᵒᵖ).unit.app M) := by
    dsimp only [Adjunction.whiskerRight]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

private theorem exact_unit_iso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] {L : C ⥤ D} {R : D ⥤ C}
    [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : L ⊣ R) [IsIso a.unit] (d : L.mapDerivedCategory ⊣ R.mapDerivedCategory) :
    IsIso d.unit :=
  d.isIso_unit_of_iso ((Functor.mapDerivedCategoryCompIso L R).symm ≪≫
    Functor.mapDerivedCategoryNatIso (asIso a.unit).symm ≪≫
    Functor.mapDerivedCategoryIdIso C)

-- Scalar restriction identifies constant-ring modules with fixed-module sheaves.
private noncomputable def fixedPresheaf (X : Scheme.{u}) :
    (X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} B) ⥤
      PresheafOfModules.{u + 1} ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of B)) where
  obj F :=
    { obj := F.obj
      map f := F.map f
      map_id U := by ext x; exact ConcreteCategory.congr_hom (F.map_id U) x
      map_comp f g := by ext x; exact ConcreteCategory.congr_hom (F.map_comp f g) x }
  map f :=
    { app := f.app
      naturality g := by ext x; exact ConcreteCategory.congr_hom (f.naturality g) x }

private noncomputable def fixedRestriction (X : Scheme.{u}) :
    Modules B X ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B) where
  obj M := by
    let P := (PresheafOfModules.restrictScalars (scalarUnit B X)).obj M.val
    let F : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} B :=
      { obj := P.obj
        map := P.map
        map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by
          ext x
          exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp _ F
      (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}) M.isSheaf⟩
  map f := { hom :=
    { app U := (ModuleCat.restrictScalars ((scalarUnit B X).app U).hom).map (f.val.app U)
      naturality _ _ g := by ext x; exact PresheafOfModules.naturality_apply f.val g x } }

private instance fixedRestriction_faithful (X : Scheme.{u}) :
    (fixedRestriction B X).Faithful where
  map_injective h := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    exact ConcreteCategory.congr_hom (congr_app (congrArg (fun k ↦ k.hom) h) U) x

private instance scalarUnit_injective (X : Scheme.{u}) :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology X) (scalarUnit B X) := by
  rw [← Presheaf.isLocallyInjective_forget_iff]
  change Presheaf.IsLocallyInjective (Scheme.ProEt.topology X)
    (Functor.whiskerRight (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B))) (forget CommRingCat.{u + 1}))
  infer_instance

private instance scalarUnit_surjective' (X : Scheme.{u}) :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) (scalarUnit B X) :=
  scalarUnit_surjective B X

set_option backward.isDefEq.respectTransparency false in
private instance fixedRestriction_full (X : Scheme.{u}) :
    (fixedRestriction B X).Full where
  map_surjective {M N} f := by
    let a : (PresheafOfModules.restrictScalars (scalarUnit B X)).obj M.val ⟶
        (PresheafOfModules.restrictScalars (scalarUnit B X)).obj N.val :=
      { app := f.hom.app
        naturality g := by ext x; exact ConcreteCategory.congr_hom (f.hom.naturality g) x }
    let R := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)
    let H := SheafOfModules.forget.{u + 1} R ⋙
      PresheafOfModules.restrictScalars.{u + 1} (scalarUnit B X)
    have : H.Full := inferInstance
    obtain ⟨b, hb⟩ := H.map_surjective a
    refine ⟨b, ?_⟩
    ext U x
    exact ConcreteCategory.congr_hom (congrArg (fun t ↦ t.app U) hb) x

set_option backward.isDefEq.respectTransparency false in
private instance fixedRestriction_essSurj (X : Scheme.{u}) :
    (fixedRestriction B X).EssSurj where
  mem_essImage F := by
    let P := (fixedPresheaf B X).obj F.obj
    let R := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)
    let M := (PresheafOfModules.sheafification.{u + 1} (R := R) (scalarUnit B X)).obj P
    let a := (PresheafOfModules.sheafificationAdjunction.{u + 1} (R := R)
      (scalarUnit B X)).unit.app P
    let f : F ⟶ (fixedRestriction B X).obj M :=
      ⟨{ app := a.app
         naturality _ _ g := by ext x; exact PresheafOfModules.naturality_apply a g x }⟩
    let H := sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1})
    have : IsIso (H.map f) := by
      have : IsIso ((sheafToPresheaf _ _).map (H.map f)) :=
        isIso_toSheafify _ (H.obj F).property
      exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)
    have : IsIso f := isIso_of_reflects_iso _ H
    exact ⟨M, ⟨(asIso f).symm⟩⟩

private noncomputable def fixedEquivalence (X : Scheme.{u}) :
    Modules B X ≌ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B) := by
  have : (fixedRestriction B X).IsEquivalence := {}
  exact (fixedRestriction B X).asEquivalence

private theorem sheaf_iso_of_bijective
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    {F G : Sheaf J (ModuleCat.{u + 1} B)} (f : F ⟶ G)
    (h : ∀ U, Function.Bijective (f.hom.app U)) : IsIso f := by
  have hi (U) : IsIso (f.hom.app U) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (h U)
  have : IsIso ((sheafToPresheaf J (ModuleCat.{u + 1} B)).map f) := by
    change IsIso f.hom
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso f (sheafToPresheaf J (ModuleCat.{u + 1} B))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedDirect {X Y : Scheme.{u}} (f : X ⟶ Y) :
    moduleDirectImage B f ⋙ fixedRestriction B Y ≅
      fixedRestriction B X ⋙ lowerStar (ModuleCat.{u + 1} B) f := by
  let a : moduleDirectImage B f ⋙ fixedRestriction B Y ⟶
      fixedRestriction B X ⋙ lowerStar (ModuleCat.{u + 1} B) f :=
    { app M :=
        ⟨{ app U := ModuleCat.homMk
            (M := ((fixedRestriction B Y).obj ((moduleDirectImage B f).obj M)).obj.obj U)
            (N := ((fixedRestriction B X).obj M).obj.obj
              ((Scheme.proEtaleBaseChange f).op.obj U)) (𝟙 _)
            (fun b ↦ by
              ext m
              exact (moduleDirectImage_scalarUnit B f M U b m).symm)
           naturality := by intros; ext; rfl }⟩
      naturality := by intros; ext; rfl }
  have hi (M) : IsIso (a.app M) :=
    sheaf_iso_of_bijective B (Scheme.ProEt.topology Y) (a.app M)
      (fun _ ↦ Function.bijective_id)
  have : IsIso a := NatIso.isIso_of_isIso_app _
  exact asIso a

private noncomputable def inverseSquare
    {A₁ A₂ C₁ C₂ : Type*} [Category A₁] [Category A₂] [Category C₁] [Category C₂]
    (eA : A₁ ≌ A₂) (eC : C₁ ≌ C₂) (F : A₁ ⥤ C₁) (H : A₂ ⥤ C₂)
    (s : eA.functor ⋙ H ≅ F ⋙ eC.functor) : H ⋙ eC.inverse ≅ eA.inverse ⋙ F :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight eA.counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft eA.inverse
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight s eC.inverse ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ eC.unitIso.symm ≪≫ Functor.rightUnitor _)

private noncomputable def leftAdjointSquare
    {A₁ A₂ C₁ C₂ : Type*} [Category A₁] [Category A₂] [Category C₁] [Category C₂]
    (eA : A₁ ≌ A₂) (eC : C₁ ≌ C₂) {F : A₁ ⥤ C₁} {R : C₁ ⥤ A₁}
    {H : A₂ ⥤ C₂} {S : C₂ ⥤ A₂} (a : F ⊣ R) (b : H ⊣ S)
    (s : R ⋙ eA.functor ≅ eC.functor ⋙ S) :
    F ⋙ eC.functor ≅ eA.functor ⋙ H :=
  ((a.comp eC.toAdjunction).ofNatIsoRight
    (inverseSquare eC eA R S s.symm).symm).leftAdjointUniq (eA.toAdjunction.comp b)

private noncomputable def cancelSquare
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    (P : A ⥤ A') (Q : B ⥤ B') (R : C ⥤ C') (S : D ⥤ D')
    [S.Full] [S.Faithful]
    (F' : A' ⥤ B') (G' : B' ⥤ D') (H' : A' ⥤ C') (I' : C' ⥤ D')
    (f : F ⋙ Q ≅ P ⋙ F') (g : G ⋙ S ≅ Q ⋙ G')
    (h : H ⋙ R ≅ P ⋙ H') (i : I ⋙ S ≅ R ⋙ I')
    (e : F' ⋙ G' ≅ H' ⋙ I') : F ⋙ G ≅ H ⋙ I := by
  apply ((Functor.FullyFaithful.ofFullyFaithful S).whiskeringRight A).preimageIso
  exact Functor.associator F G S ≪≫ Functor.isoWhiskerLeft F g ≪≫
    (Functor.associator F Q G').symm ≪≫ Functor.isoWhiskerRight f G' ≪≫
    Functor.associator P F' G' ≪≫ Functor.isoWhiskerLeft P e ≪≫
    (Functor.associator P H' I').symm ≪≫ Functor.isoWhiskerRight h.symm I' ≪≫
    Functor.associator H R I' ≪≫ Functor.isoWhiskerLeft H i.symm ≪≫
    (Functor.associator H I S).symm

private noncomputable def cancelIso
    {A D A' D' : Type*} [Category A] [Category D] [Category A'] [Category D']
    (F G : A ⥤ D) (P : A ⥤ A') (S : D ⥤ D') [S.Full] [S.Faithful]
    (F' G' : A' ⥤ D') (f : F ⋙ S ≅ P ⋙ F') (g : G ⋙ S ≅ P ⋙ G')
    (e : F' ≅ G') : F ≅ G :=
  ((Functor.FullyFaithful.ofFullyFaithful S).whiskeringRight A).preimageIso
    (f ≪≫ Functor.isoWhiskerLeft P e ≪≫ g.symm)

private noncomputable def fixedPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modulePullback B f ⋙ fixedRestriction B X ≅
      fixedRestriction B Y ⋙ upperStar (ModuleCat.{u + 1} B) f :=
  leftAdjointSquare (fixedEquivalence B Y) (fixedEquivalence B X)
    (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f) (fixedDirect B f)

private noncomputable def fixedOpen {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    moduleJ B j ⋙ fixedRestriction B X ≅
      fixedRestriction B U ⋙ openImmersionLowerShriek (ModuleCat.{u + 1} B) j :=
  leftAdjointSquare (fixedEquivalence B U) (fixedEquivalence B X)
    (moduleJAdj B j) (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (fixedPull B j)

@[irreducible] private noncomputable def moduleOpenSquare {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (hsq : IsPullback a j' j g) :
    moduleJ B j ⋙ modulePullback B g ≅ modulePullback B a ⋙ moduleJ B j' := by
  exact cancelSquare (moduleJ B j) (modulePullback B g)
    (modulePullback B a) (moduleJ B j')
    (fixedRestriction B U) (fixedRestriction B X) (fixedRestriction B U')
    (fixedRestriction B X') (openImmersionLowerShriek (ModuleCat.{u + 1} B) j)
    (upperStar (ModuleCat.{u + 1} B) g) (upperStar (ModuleCat.{u + 1} B) a)
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) j')
    (fixedOpen B j) (fixedPull B g) (fixedPull B a) (fixedOpen B j')
    (openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} B) hsq).symm

@[irreducible] private noncomputable def moduleClopenIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j] : moduleJ B j ≅ moduleDirectImage B j := by
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
    (ModuleCat.{u + 1} B) j j.isClosedEmbedding.isClosed_range
  exact cancelIso (moduleJ B j) (moduleDirectImage B j)
    (fixedRestriction B U) (fixedRestriction B X)
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) j) (lowerStar (ModuleCat.{u + 1} B) j)
    (fixedOpen B j) (fixedDirect B j)
    (asIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} B) j))

/-- Canonical comparison of the two iterated inverse images around any commutative square.
Source: Stacks, Tag 07A7 (blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def squareG {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    G B i ⋙ G B r ≅ G B p ⋙ G B k :=
  (gComp B r i).symm ≪≫ eqToIso (congrArg (G B) h.symm) ≪≫ gComp B k p

/-- The inverse cartesian open comparison is defined by precisely the open-unit transpose.
Source: Stacks, Tags 09AE and 07A7
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def betaInvApp {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (M : Derived B U) :
    (J B j').obj ((G B gU).obj M) ⟶ (G B g).obj ((J B j).obj M) :=
  ((jAdj B j').homEquiv _ _).symm
    ((G B gU).map ((jAdj B j).unit.app M) ≫
      (squareG B gU j' j g h).inv.app ((J B j).obj M))

/-- Naturality of the specified open-unit transpose. Source: Stacks, Tag 09AE
(blueprint: def-cbc-strict-tower-proper-open-arrows).
Proof: use naturality of the open unit, the pullback compositor and the adjunction
Hom equivalence. The transposes of both sides are the same naturality square. -/
theorem betaInvApp_naturality {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (M N : Derived B U) (f : M ⟶ N) :
    (G B gU ⋙ J B j').map f ≫ betaInvApp B gU j' j g h N =
      betaInvApp B gU j' j g h M ≫ (J B j ⋙ G B g).map f := by
  apply (jAdj B j').homEquiv_naturality_right_square
  exact ((Functor.whiskerRight (jAdj B j).unit (G B gU)) ≫
    Functor.whiskerLeft (J B j) (squareG B gU j' j g h).inv).naturality f

/-- The inverse comparison as a natural transformation with the specified transpose.
Source: Stacks, Tag 09AE (blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def betaInv {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g) :
    G B gU ⋙ J B j' ⟶ J B j ⋙ G B g where
  app := betaInvApp B gU j' j g h
  naturality := betaInvApp_naturality B gU j' j g h

/-- The open-extension unit is invertible. Source: Stacks, Tags 03DI and 09AE
(blueprint: def-cbc-strict-tower-proper-open-arrows).
Proof: on an object lying over the open there is exactly one lift to it, so restriction
of the extension presheaf is the original module. This survives sheafification,
termwise extension to strict towers, and exact localization. -/
theorem jAdj_unit_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (jAdj B j).unit := by
  let A := ModuleCat.{u + 1} B
  have : IsIso (openImmersionLowerShriekAdjunction A j).unit :=
    (openImmersionAdjunctionTriple A j).isIso_unit_iff_isIso_counit.mpr
      (isIso_openImmersionRestrictionLowerStarAdjunction_counit A j)
  let ff := (openImmersionLowerShriekAdjunction A j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : IsIso (moduleJAdj B j).unit :=
    unit_iso_of_comparison (L := moduleJ B j) (R := modulePullback B j)
      (moduleJAdj B j) (fixedRestriction B U) (fixedRestriction B X)
      (openImmersionLowerShriek A j) (fixedOpen B j)
  have : IsIso (((moduleJAdj B j).whiskerRight ℕᵒᵖ).unit) :=
    tower_unit_iso (moduleJAdj B j)
  exact exact_unit_iso (C := Towers B U) (D := Towers B X)
    (L := towerJ B j) (R := towerPullback B j)
    ((moduleJAdj B j).whiskerRight ℕᵒᵖ) (jAdj B j)

@[irreducible] private noncomputable def derivedOpenSquare {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (hsq : IsPullback gU j' j g) :
    J B j ⋙ G B g ≅ G B gU ⋙ J B j' := by
  exact Functor.mapDerivedCategorySquareIso
    (F₁ := towerJ B j) (F₂ := towerPullback B g)
    (G₁ := towerPullback B gU) (G₂ := towerJ B j')
    (towerSquare (moduleJ B j) (modulePullback B g) (modulePullback B gU)
      (moduleJ B j') (moduleOpenSquare B gU j' j g hsq))

/-- The unit-normalized comparison is invertible for a cartesian open square and
arbitrary B. Source: Stacks, Tag 09AE and blueprint, second proof step
(blueprint: def-cbc-strict-tower-proper-open-arrows).
Proof: transport ordinary open base change through the equivalence between constant-ring
modules and sheaves of fixed B-modules, then extend termwise and localize. Thus G_g J_j M
lies in the essential image of the fully faithful J_jprime. The specified transpose is
its invertible counit composed with J_jprime of the pulled-back invertible open unit. -/
theorem betaInv_isIso {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (hsq : IsPullback gU j' j g) : IsIso (betaInv B gU j' j g h) := by
  have := jAdj_unit_isIso B j
  have := jAdj_unit_isIso B j'
  let ff := (jAdj B j').fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  let d := derivedOpenSquare B gU j' j g hsq
  have hi (M : Derived B U) : IsIso ((betaInv B gU j' j g h).app M) := by
    have hc : IsIso ((jAdj B j').counit.app ((G B g).obj ((J B j).obj M))) :=
      (jAdj B j').isIso_counit_app_of_iso (d.app M)
    have hu : IsIso ((jAdj B j).unit.app M) := inferInstance
    change IsIso (betaInvApp B gU j' j g h M)
    unfold betaInvApp
    rw [Adjunction.homEquiv_counit]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- Cartesian open base change, oriented as G_g j_! → j'_! G_gU.
Source: Stacks, Tag 09AE (blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def beta {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (hsq : IsPullback gU j' j g) : J B j ⋙ G B g ≅ G B gU ⋙ J B j' :=
  (@asIso _ _ _ _ (betaInv B gU j' j g h)
    (betaInv_isIso B gU j' j g h hsq)).symm

/-- The map of a proper/open commutative square into its canonical fibre product.
Source: Stacks, Tag 0F7B and blueprint, third proof step
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable abbrev squareLift {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) := pullback.lift k r h

/-- The induced lift is open and closed; no cartesian or identity-left assumption.
Source: Stacks, Tags 01W6 and 01IQ, and blueprint, third proof step
(blueprint: def-cbc-strict-tower-proper-open-arrows).
Proof: identify the fibre product with p⁻¹(S), an open in W. The map s identifies V
with k(V) inside this open. The base change q of p is separated and q s = r is
proper, so the proper-over-separated theorem makes s proper. A proper open immersion
is closed. This includes the empty open and gives the complementary open component. -/
theorem squareLift_clopen {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    IsOpenImmersion (squareLift k r p i h) ∧ IsClosedImmersion (squareLift k r p i h) := by
  have hopen : IsOpenImmersion (squareLift k r p i h) := by
    have : IsOpenImmersion (squareLift k r p i h ≫ pullback.fst p i) := by
      simpa only [squareLift, pullback.lift_fst] using (inferInstance : IsOpenImmersion k)
    exact IsOpenImmersion.of_comp _ (pullback.fst p i)
  have hproper : IsProper (squareLift k r p i h) := by
    have : IsProper (squareLift k r p i h ≫ pullback.snd p i) := by
      simpa only [squareLift, pullback.lift_snd] using (inferInstance : IsProper r)
    exact IsProper.of_comp _ (pullback.snd p i)
  exact ⟨hopen, IsClosedImmersion.of_isPreimmersion _
    ((squareLift k r p i h).isClosedMap.isClosed_range)⟩

/-- Open part of the clopen factorization. Source: Stacks, Tags 01W6 and 01IQ
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable instance squareLift_open {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : IsOpenImmersion (squareLift k r p i h) :=
  (squareLift_clopen k r p i h).1

/-- Closed part of the clopen factorization. Source: Stacks, Tags 01W6 and 01IQ
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable instance squareLift_closed {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : IsClosedImmersion (squareLift k r p i h) :=
  (squareLift_clopen k r p i h).2

/-- The canonical map from open extension to direct image is the counit mate of the
inverse open unit. Source: Stacks, Tags 03DI and 09AE
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def openToR {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    J B j ⟶ R B j :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft (J B j) (adj B j).unit ≫
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (@inv _ _ _ _ (jAdj B j).unit (jAdj_unit_isIso B j)) (R B j) ≫
          (Functor.leftUnitor _).hom

@[irreducible] private noncomputable def derivedClopenIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j] : J B j ≅ R B j := by
  let e : towerJ B j ≅ towerDirectImage B j :=
    (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (moduleClopenIso B j)
  have : PreservesFiniteLimits (towerDirectImage B j) :=
    preservesFiniteLimits_of_natIso e
  have : PreservesFiniteColimits (towerDirectImage B j) :=
    preservesFiniteColimits_of_natIso e
  exact Functor.mapDerivedCategoryNatIso e ≪≫
    (towerDirectImage B j).rightDerivedFunctorIsoMapDerivedCategory.symm

/-- For a clopen immersion the canonical open-to-direct-image comparison is invertible.
Source: Stacks, Tag 09AE and blueprint, fourth proof step
(blueprint: def-cbc-strict-tower-proper-open-arrows).
Proof: transport the ordinary clopen extension/direct-image isomorphism through the
constant-ring module equivalence. Termwise direct image is therefore exact, so its
right derived functor R is isomorphic to J and is fully faithful. The direct-image
adjunction unit is invertible on J M, which lies in the essential image of R. The
specified comparison is this unit followed by R of the inverse open unit. -/
theorem openToR_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [IsClosedImmersion j] : IsIso (openToR B j) := by
  let d := derivedClopenIso B j
  have := jAdj_unit_isIso B j
  let ff := (jAdj B j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : (R B j).Full := Functor.Full.of_iso d
  have : (R B j).Faithful := Functor.Faithful.of_iso d
  have hi (M : Derived B U) : IsIso ((openToR B j).app M) := by
    have hu : IsIso ((adj B j).unit.app ((J B j).obj M)) :=
      (adj B j).isIso_unit_app_of_iso (d.app M)
    have hv : IsIso ((inv (jAdj B j).unit).app M) := inferInstance
    have hw : IsIso ((R B j).map ((inv (jAdj B j).unit).app M)) := inferInstance
    dsimp only [openToR, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_inv_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app]
    simp only [Category.id_comp]
    exact IsIso.comp_isIso' hu (IsIso.comp_isIso' hw (IsIso.id _))
  exact NatIso.isIso_of_isIso_app _

/-- The intrinsic clopen component projection, with no arbitrary splitting choice.
Source: Stacks, Tag 09AE and blueprint, fourth proof step
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def pi {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
    [IsClosedImmersion s] : 𝟭 (Derived B X) ⟶ G B s ⋙ J B s :=
  (adj B s).unit ≫ Functor.whiskerLeft (G B s)
    (@inv _ _ _ _ (openToR B s) (openToR_isIso B s))

/-- The normalized non-cartesian open comparison uses beta and the intrinsic clopen
projection, followed by the open and pullback compositors. Source: Stacks, Tag 0F7B
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def alpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : J B i ⋙ G B p ⟶ G B r ⋙ J B k :=
  (beta B (pullback.snd p i) (pullback.fst p i) i p
    (pullback.condition.symm) (IsPullback.of_hasPullback p i).flip).hom ≫
  Functor.whiskerRight (Functor.whiskerLeft (G B (pullback.snd p i))
    (pi B (squareLift k r p i h))) (J B (pullback.fst p i)) ≫
  Functor.whiskerRight
    (Functor.associator (G B (pullback.snd p i)) (G B (squareLift k r p i h))
      (J B (squareLift k r p i h))).inv (J B (pullback.fst p i)) ≫
  (Functor.associator (G B (pullback.snd p i) ⋙ G B (squareLift k r p i h))
    (J B (squareLift k r p i h)) (J B (pullback.fst p i))).hom ≫
  Functor.whiskerLeft (G B (pullback.snd p i) ⋙ G B (squareLift k r p i h))
    ((jComp B (squareLift k r p i h) (pullback.fst p i)).hom ≫
      (jCongr B (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight
    ((gComp B (squareLift k r p i h) (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (G B) (pullback.lift_snd k r h))).hom) (J B k)

end AlgebraicGeometry.ProEtale.StrictTower
