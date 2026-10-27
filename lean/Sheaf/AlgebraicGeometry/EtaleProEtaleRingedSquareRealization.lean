/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
public import Sheaf.CategoryTheory.SiteModuleSheafConstantRingEquivalence
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

import Sheaf.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The constant-ring realization of the etale/pro-etale comparison square

Source: Stacks Project, proetale.tex, Section 09A5, square preceding Tag 09A6;
sites.tex, Tags 00YV and 0H7J; sites-modules.tex, Tags 03D2 and 03D3.
(blueprint: lem-sfb-etale-proetale-ringed-square-realization).

The four edges retain the actual sites and the constant-section structure maps.
Their module pullbacks are the adjoints to the actual ringed module direct images.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.SfbRingedSquare

/-- The four corners of the specified square.
Source: Stacks 09A5 (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
inductive Corner where
  | yEt | xEt | yPro | xPro

/-- The four edges, in the direction of inverse image.
Source: Stacks 09A5 (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
inductive Edge where
  | etale | proetale | comparisonX | comparisonY

/-- The original small sites, without equating their object and morphism universes.
Source: Stacks 09A5 (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
abbrev Site (X Y : Scheme.{u}) : Corner → Type (u + 1)
  | .yEt => Y.Etale
  | .xEt => X.Etale
  | .yPro => Y.ProEt
  | .xPro => X.ProEt

/-- The inherited site categories.
Source: Stacks 09A5 (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
instance siteCategory (X Y : Scheme.{u}) (c : Corner) : Category.{u} (Site X Y c) :=
  match c with
  | .yEt => inferInstanceAs (Category.{u} Y.Etale)
  | .xEt => inferInstanceAs (Category.{u} X.Etale)
  | .yPro => inferInstanceAs (Category.{u} Y.ProEt)
  | .xPro => inferInstanceAs (Category.{u} X.ProEt)

/-- The topology already fixed at each corner.
Source: Stacks 09A5 (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
def topology (X Y : Scheme.{u}) : (c : Corner) → GrothendieckTopology (Site X Y c)
  | .yEt => Y.smallEtaleTopology
  | .xEt => X.smallEtaleTopology
  | .yPro => Scheme.ProEt.topology Y
  | .xPro => Scheme.ProEt.topology X

/-- Domain corner of an inverse-image edge.
Source: Stacks 09A5 (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
def fromCorner : Edge → Corner
  | .etale => .yEt
  | .proetale => .yPro
  | .comparisonX => .xEt
  | .comparisonY => .yEt

/-- Codomain corner of an inverse-image edge.
Source: Stacks 09A5 (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
def toCorner : Edge → Corner
  | .etale => .xEt
  | .proetale => .xPro
  | .comparisonX => .xPro
  | .comparisonY => .yPro

/-- The specified base-change functors and inclusions, on schemes and arrows.
Source: Stacks 09A5 (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
def siteFunctor {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (e : Edge) → Site X Y (fromCorner e) ⥤ Site X Y (toCorner e)
  | .etale => MorphismProperty.Over.pullback @Etale ⊤ p
  | .proetale => Scheme.proEtaleBaseChange p
  | .comparisonX => Scheme.toProEt X
  | .comparisonY => Scheme.toProEt Y

/-- Continuity of the four specified site functors.
Source: Stacks 09A5 (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
instance siteFunctorContinuous {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) :
    (siteFunctor p e).IsContinuous (topology X Y (fromCorner e))
      (topology X Y (toCorner e)) :=
  match e with
  | .etale => Etale.isContinuous_overPullback p
  | .proetale => Scheme.proEtaleBaseChange_isContinuous p
  | .comparisonX => Scheme.isContinuous_toProEt X
  | .comparisonY => Scheme.isContinuous_toProEt Y

/-- Sheafification at these original sites, with the common coefficient universe.
Source: Stacks 00YV (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
instance ringSheafify (X Y : Scheme.{u}) (c : Corner) :
    HasWeakSheafify (topology X Y c) RingCat.{u + 1} := by
  cases c <;> dsimp [topology] <;> infer_instance

/-- The constant ring sheaf, with its canonical sheafification unit.
Source: Stacks 0H7J (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
abbrev RingSheaf (A : Type (u + 1)) [CommRing A] (X Y : Scheme.{u}) (c : Corner) :=
  (constantSheaf (topology X Y c) RingCat.{u + 1}).obj (RingCat.of A)

/-- The structural direct-image map is the extension of the constant-section map.
Source: Stacks 0H7J (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
def ringDirectMap (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (e : Edge) : RingSheaf A X Y (fromCorner e) ⟶
      ((siteFunctor p e).sheafPushforwardContinuous RingCat.{u + 1}
        (topology X Y (fromCorner e)) (topology X Y (toCorner e))).obj
          (RingSheaf A X Y (toCorner e)) :=
  ((sheafificationAdjunction (topology X Y (fromCorner e)) RingCat.{u + 1}).homEquiv
    _ _).symm (Functor.whiskerLeft (siteFunctor p e).op
      (toSheafify (topology X Y (toCorner e))
        ((Functor.const (Site X Y (toCorner e))ᵒᵖ).obj (RingCat.of A))))

/-- Ring inverse image is Kan extension followed by sheafification.
Source: Stacks 00WX (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
abbrev ringPull {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) :=
  Functor.sheafPullbackConstruction.sheafPullback (siteFunctor p e) RingCat.{u + 1}
    (topology X Y (fromCorner e)) (topology X Y (toCorner e))

/-- The actual ring-sheaf adjunction for an edge.
Source: Stacks 00WX (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
abbrev ringAdj {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (siteFunctor p e)
    RingCat.{u + 1} (topology X Y (fromCorner e)) (topology X Y (toCorner e))

/-- The structural inverse-image map is the transpose of the constant-section map.
Source: Stacks 0H7J (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
def ringMap (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (e : Edge) : (ringPull p e).obj (RingSheaf A X Y (fromCorner e)) ⟶
      RingSheaf A X Y (toCorner e) :=
  ((ringAdj p e).homEquiv _ _).symm (ringDirectMap A p e)

private theorem ringDirectMap_unit (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) :
    toSheafify (topology X Y (fromCorner e))
        ((Functor.const (Site X Y (fromCorner e))ᵒᵖ).obj (RingCat.of A)) ≫
      (ringDirectMap A p e).hom =
        Functor.whiskerLeft (siteFunctor p e).op
          (toSheafify (topology X Y (toCorner e))
            ((Functor.const (Site X Y (toCorner e))ᵒᵖ).obj (RingCat.of A))) := by
  exact ((sheafificationAdjunction (topology X Y (fromCorner e))
    RingCat.{u + 1}).homEquiv _ _).apply_symm_apply _

private instance siteHasTerminal (X Y : Scheme.{u}) (c : Corner) :
    HasTerminal (Site X Y c) := by
  cases c <;> dsimp [Site] <;> infer_instance

private instance siteFunctorFiniteLimits {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) :
    PreservesFiniteLimits (siteFunctor p e) := by
  cases e with
  | etale => exact inferInstanceAs
      (PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ p))
  | proetale => exact inferInstanceAs (PreservesFiniteLimits (Scheme.proEtaleBaseChange p))
  | comparisonX => exact Scheme.preservesFiniteLimits_toProEt X
  | comparisonY => exact Scheme.preservesFiniteLimits_toProEt Y

private theorem ringMap_isIso (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) : IsIso (ringMap A p e) := by
  let J := topology X Y (fromCorner e)
  let K := topology X Y (toCorner e)
  let F := siteFunctor p e
  let T := ⊤_ (Site X Y (fromCorner e))
  have hT : IsTerminal T := terminalIsTerminal
  have hFT : IsTerminal (F.obj T) := hT.isTerminalObj F _
  let aJ := constantSheafAdj J RingCat.{u + 1} hT
  let adj := (aJ.comp (ringAdj p e)).ofNatIsoRight
    (F.sheafPushforwardContinuousCompSheafSectionsObjIso RingCat.{u + 1} J K
      (Opposite.op T))
  let i := adj.leftAdjointUniq (constantSheafAdj K RingCat.{u + 1} hFT)
  have hi : i.hom.app (RingCat.of A) = ringMap A p e := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [adj, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    dsimp only [Functor.sheafPushforwardContinuousCompSheafSectionsObjIso]
    erw [Category.comp_id, Equiv.trans_apply, Equiv.apply_symm_apply]
    dsimp only [aJ, constantSheafAdj, ringDirectMap]
    erw [Adjunction.comp_homEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
    erw [Adjunction.comp_unit_app, Adjunction.homEquiv_unit]
    simp only [constantPresheafAdj_unit_app, Category.id_comp]
    rfl
  rw [← hi]
  infer_instance

private theorem coefficientDirectImage_hom_app
    (D : Type*) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology D]
    [∀ Z : Scheme.{u}, HasWeakSheafify (Scheme.ProEt.topology Z) D]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (N : Sheaf (Scheme.ProEt.topology X) D) (U : Y.Etaleᵒᵖ) :
    ((supportSiteComparisonCoefficientDirectImageIso D p).hom.app N).hom.app U = 𝟙 _ := by
  simp only [supportSiteComparisonCoefficientDirectImageIso,
    supportSiteComparisonSiteBaseChangeIso, Iso.trans_hom,
    Functor.sheafPushforwardContinuousIso_hom, Iso.refl_inv, Iso.symm_hom,
    NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousNatTrans_app_hom,
    Functor.sheafPushforwardContinuousComp_hom_app_hom_app,
    Functor.sheafPushforwardContinuousComp_inv_app_hom_app]
  dsimp only [Functor.whiskerRight_app, NatTrans.op_app, NatTrans.id_app]
  erw [Category.id_comp, Category.comp_id]
  change N.obj.map (𝟙 _) = 𝟙 _
  exact N.obj.map_id _

private theorem compAdjunct
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {X : C} {Y : D} {Z : E} (f : X ⟶ R₁.obj Y) (g : Y ⟶ R₂.obj Z) :
    (adj₁.comp adj₂).homEquiv X Z
      (L₂.map ((adj₁.homEquiv X Y).symm f) ≫ (adj₂.homEquiv Y Z).symm g) =
      f ≫ R₁.map g := by
  rw [Adjunction.comp_homEquiv]
  change adj₁.homEquiv X (R₂.obj Z)
    (adj₂.homEquiv (L₁.obj X) Z
      (L₂.map ((adj₁.homEquiv X Y).symm f) ≫ (adj₂.homEquiv Y Z).symm g)) = _
  rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]

private theorem squareAdjunct
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (δ : R₂ ⟶ R₁)
    {X : C} {Y : D} (g : L₂.obj X ⟶ Y) :
    adj₁.homEquiv X Y (((conjugateEquiv adj₂ adj₁).symm δ).app X ≫ g) =
      adj₂.homEquiv X Y g ≫ δ.app Y := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv_symm adj₂ adj₁, Category.assoc, ← δ.naturality,
    ← Category.assoc, ← Adjunction.homEquiv_unit]

/-- The four constant-section structural maps are invertible and obey the ring equation.
Source: Stacks 09A5, square preceding 09A6, and 0H7J
(blueprint: lem-sfb-etale-proetale-ringed-square-realization).
Proof: each inverse image preserves constants by the geometric constant-module theorem.
Uniqueness of maps out of a constant sheaf identifies its coefficient isomorphism with
ringMap. Naturality of the geometric square on every constant section makes the two
paths identical; the constant-sheaf/global-sections adjunction detects that equality.
This includes the zero ring and the empty scheme and uses no cartesianness assumption. -/
theorem coefficients (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (∀ e : Edge, IsIso (ringMap A p e)) ∧
      (ringPull p .comparisonX).map (ringMap A p .etale) ≫ ringMap A p .comparisonX =
        (supportSiteComparisonCoefficientPullbackIso RingCat.{u + 1} p).hom.app
            (RingSheaf A X Y .yEt) ≫
          (ringPull p .proetale).map (ringMap A p .comparisonY) ≫
            ringMap A p .proetale := by
  refine ⟨ringMap_isIso A p, ?_⟩
  let adj₁ := (ringAdj p .etale).comp (ringAdj p .comparisonX)
  let adj₂ := (ringAdj p .comparisonY).comp (ringAdj p .proetale)
  let R₁ := ((siteFunctor p .comparisonX).sheafPushforwardContinuous RingCat.{u + 1}
      (topology X Y (fromCorner .comparisonX)) (topology X Y (toCorner .comparisonX))) ⋙
    ((siteFunctor p .etale).sheafPushforwardContinuous RingCat.{u + 1}
      (topology X Y (fromCorner .etale)) (topology X Y (toCorner .etale)))
  let δ := supportSiteComparisonCoefficientDirectImageIso RingCat.{u + 1} p
  have h₁ := compAdjunct (ringAdj p .etale) (ringAdj p .comparisonX)
    (ringDirectMap A p .etale) (ringDirectMap A p .comparisonX)
  have h₃ := compAdjunct (ringAdj p .comparisonY) (ringAdj p .proetale)
    (ringDirectMap A p .comparisonY) (ringDirectMap A p .proetale)
  have h₂ := squareAdjunct adj₁ adj₂ δ.hom
    ((ringPull p .proetale).map (ringMap A p .comparisonY) ≫ ringMap A p .proetale)
  apply (adj₁.homEquiv _ _).injective
  change _ = adj₁.homEquiv _ _
    ((supportSiteComparisonCoefficientPullbackIso RingCat.{u + 1} p).hom.app
      (RingSheaf A X Y .yEt) ≫ _)
  erw [h₁, h₂, h₃]
  apply ((sheafificationAdjunction (topology X Y .yEt) RingCat.{u + 1}).homEquiv
    _ _).injective
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Category.assoc]
  ext U a
  change
    (ringDirectMap A p .comparisonX).hom.app ((siteFunctor p .etale).op.obj U)
        ((ringDirectMap A p .etale).hom.app U
          ((toSheafify (topology X Y .yEt)
            ((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of A))).app U a)) =
      ((δ.hom.app (RingSheaf A X Y .xPro)).hom.app U)
        ((ringDirectMap A p .proetale).hom.app ((siteFunctor p .comparisonY).op.obj U)
          ((ringDirectMap A p .comparisonY).hom.app U
            ((toSheafify (topology X Y .yEt)
              ((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of A))).app U a)))
  have he := congrArg (fun f ↦ f a)
    (NatTrans.congr_app (ringDirectMap_unit A p .etale) U)
  have hy := congrArg (fun f ↦ f a)
    (NatTrans.congr_app (ringDirectMap_unit A p .comparisonY) U)
  have hx := congrArg (fun f ↦ f a)
    (NatTrans.congr_app (ringDirectMap_unit A p .comparisonX)
      ((siteFunctor p .etale).op.obj U))
  have hp := congrArg (fun f ↦ f a)
    (NatTrans.congr_app (ringDirectMap_unit A p .proetale)
      ((siteFunctor p .comparisonY).op.obj U))
  erw [he, hy, hx, hp]
  erw [coefficientDirectImage_hom_app]
  rfl

/-- Abelian sheafification on each original site.
Source: Stacks 00YV (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
instance abSheafify (X Y : Scheme.{u}) (c : Corner) :
    HasWeakSheafify (topology X Y c) AddCommGrpCat.{u + 1} := by
  cases c <;> dsimp [topology] <;> infer_instance

/-- The locally bijective description of additive sheafification.
Source: Stacks 00YV (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
instance abLocallyBijective (X Y : Scheme.{u}) (c : Corner) :
    (topology X Y c).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}
    (J := topology X Y c)

/-- Sheafification with fixed coefficients, in the same universe as the ring sheaves.
Source: Stacks 00YV (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
instance fixedSheafify (A : Type (u + 1)) [CommRing A] (X Y : Scheme.{u}) (c : Corner) :
    HasWeakSheafify (topology X Y c) (ModuleCat.{u + 1} A) := by
  cases c <;> dsimp [topology] <;> infer_instance

/-- The existing category of modules over the constant ring sheaf at a corner.
Source: Stacks 03D1 (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
abbrev Modules (A : Type (u + 1)) [CommRing A] (X Y : Scheme.{u}) (c : Corner) :=
  SheafOfModules.{u + 1} (RingSheaf A X Y c)

/-- Fixed-coefficient sheaves at a corner.
Source: Stacks 00YV (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
abbrev Fixed (A : Type (u + 1)) [CommRing A] (X Y : Scheme.{u}) (c : Corner) :=
  Sheaf (topology X Y c) (ModuleCat.{u + 1} A)

/-- The constant-section-preserving equivalence, in its canonical restriction direction.
Source: Stacks 093I (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
def restriction (A : Type (u + 1)) [CommRing A] (X Y : Scheme.{u}) (c : Corner) :
    Modules A X Y c ⥤ Fixed A X Y c :=
  constantRingModuleRestriction (topology X Y c) A

/-- The recorded constant-ring equivalence supplies this instance on the original sites.
Source: Stacks 093I (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
instance restrictionIsEquivalence (A : Type (u + 1)) [CommRing A]
    (X Y : Scheme.{u}) (c : Corner) : (restriction A X Y c).IsEquivalence :=
  let E := (constant_ring_module_sheaves (topology X Y c) A).1.choose
  letI := E.isEquivalence_functor
  Functor.isEquivalence_of_iso
    (eqToIso (constant_ring_module_sheaves (topology X Y c) A).1.choose_spec.1)

/-- Additivity is supplied by the same recorded equivalence theorem.
Source: Stacks 093I (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
instance restrictionAdditive (A : Type (u + 1)) [CommRing A]
    (X Y : Scheme.{u}) (c : Corner) : (restriction A X Y c).Additive :=
  Eq.mp (congrArg (fun F ↦ F.Additive)
    (constant_ring_module_sheaves (topology X Y c) A).1.choose_spec.1)
      (constant_ring_module_sheaves (topology X Y c) A).1.choose_spec.2.1

/-- The actual ringed module direct image, with scalars through the constant-section map.
Source: Stacks 03D1 (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
abbrev modulePush (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (e : Edge) : Modules A X Y (toCorner e) ⥤ Modules A X Y (fromCorner e) :=
  SheafOfModules.pushforward.{u + 1} (ringDirectMap A p e)

/-- The original fixed-A inverse image on an edge.
Source: Stacks 00YV (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
def fixedPull (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (e : Edge) :=
  Functor.sheafPullbackConstruction.sheafPullback (siteFunctor p e) (ModuleCat.{u + 1} A)
    (topology X Y (fromCorner e)) (topology X Y (toCorner e))

/-- Fixed-A direct image is literal restriction on sections.
Source: Stacks 00YV (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
abbrev fixedPush (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (e : Edge) :=
  (siteFunctor p e).sheafPushforwardContinuous (ModuleCat.{u + 1} A)
    (topology X Y (fromCorner e)) (topology X Y (toCorner e))

/-- The published fixed-coefficient Kan-extension adjunction.
Source: Stacks 00WX (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
abbrev fixedAdj (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (e : Edge) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (siteFunctor p e)
    (ModuleCat.{u + 1} A) (topology X Y (fromCorner e)) (topology X Y (toCorner e))

set_option backward.isDefEq.respectTransparency false in
private def directComparisonAux (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) :
    modulePush A p e ⋙ restriction A X Y (fromCorner e) ≅
      restriction A X Y (toCorner e) ⋙ fixedPush A p e := by
  have h (U : (Site X Y (fromCorner e))ᵒᵖ) (a : A) :
      (ringDirectMap A p e).hom.app U
        ((toSheafify (topology X Y (fromCorner e))
          ((Functor.const (Site X Y (fromCorner e))ᵒᵖ).obj (RingCat.of A))).app U a) =
      (toSheafify (topology X Y (toCorner e))
        ((Functor.const (Site X Y (toCorner e))ᵒᵖ).obj (RingCat.of A))).app
          ((siteFunctor p e).op.obj U) a :=
    congrArg (fun f ↦ f a) (NatTrans.congr_app (ringDirectMap_unit A p e) U)
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine { hom := ?_, inv := ?_, hom_inv_id := ?_, inv_hom_id := ?_ }
    · refine ⟨{ app := fun U ↦ ?_, naturality := ?_ }⟩
      · refine ConcreteCategory.ofHom (C := ModuleCat A) ?_
        refine
          { toFun := id
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun a x ↦ ?_ }
        change (ringDirectMap A p e).hom.app U
            ((toSheafify (topology X Y (fromCorner e))
              ((Functor.const (Site X Y (fromCorner e))ᵒᵖ).obj (RingCat.of A))).app U a) •
                (show M.val.obj ((siteFunctor p e).op.obj U) from x) = _
        rw [h]
        rfl
      · intros
        ext x
        rfl
    · refine ⟨{ app := fun U ↦ ?_, naturality := ?_ }⟩
      · refine ConcreteCategory.ofHom (C := ModuleCat A) ?_
        refine
          { toFun := id
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun a x ↦ ?_ }
        change _ = (ringDirectMap A p e).hom.app U
            ((toSheafify (topology X Y (fromCorner e))
              ((Functor.const (Site X Y (fromCorner e))ᵒᵖ).obj (RingCat.of A))).app U a) •
                (show M.val.obj ((siteFunctor p e).op.obj U) from x)
        rw [h]
        rfl
      · intros
        ext x
        rfl
    · ext U x
      rfl
    · ext U x
      rfl
  · intros
    ext U x
    rfl

/-- The four actual ringed direct images have module left adjoints.
Source: Stacks 03D2, 03D3 (blueprint: lem-sfb-etale-proetale-ringed-square-realization).
Proof: lift the Hom universes of the original sites with AsSmall. On those small
models apply the sheafified presheaf-module pullback construction. Precomposition
along the site equivalences transports the adjunction back to the original sites.
Its right adjoint is the displayed direct image, including its structural scalar map.
Equivalently use the constant-section module equivalences and the fixed-A adjunctions.
The adjunction universal property determines the left adjoint up to its unique
unit-compatible isomorphism; no arbitrary map or coefficient identification is chosen. -/
theorem modulePushIsRightAdjoint (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) :
    (modulePush A p e).IsRightAdjoint := by
  have : (fixedPush A p e).IsRightAdjoint := (fixedAdj A p e).isRightAdjoint
  have : (modulePush A p e ⋙ restriction A X Y (fromCorner e)).IsRightAdjoint :=
    Functor.isRightAdjoint_of_iso (directComparisonAux A p e).symm
  exact (Functor.isRightAdjoint_comp_iff_left _
    (restriction A X Y (fromCorner e))).mp inferInstance

attribute [instance] modulePushIsRightAdjoint

/-- The ringed module pullback, the existing left adjoint to the actual direct image.
Source: Stacks 03D2 (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
def modulePull (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) :=
  SheafOfModules.pullback.{u + 1} (ringDirectMap A p e)

/-- Its actual adjunction, fixing the module comparison by its unit.
Source: Stacks 03D3 (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
abbrev moduleAdj (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) :=
  SheafOfModules.pullbackPushforwardAdjunction.{u + 1} (ringDirectMap A p e)

/-- Scalar restriction identifies the actual module direct image with fixed-A restriction.
The identity on sections uniquely fixes this comparison.
Source: Stacks 093I, 03D1 (blueprint: lem-sfb-etale-proetale-ringed-square-realization).
Proof: the sheafification unit sends a constant a to a on every base-changed object.
Consequently restriction of its structural scalar action is the original A-action.
The identity functions on sections are linear and commute with every restriction;
they and their identity inverses give the comparison. Faithfulness of forgetting
module structure shows uniqueness. -/
theorem directComparison_existsUnique (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) :
    ∃! d : modulePush A p e ⋙ restriction A X Y (fromCorner e) ≅
        restriction A X Y (toCorner e) ⋙ fixedPush A p e,
      ∀ (M : Modules A X Y (toCorner e)) (U : (Site X Y (fromCorner e))ᵒᵖ)
        (x : M.val.obj ((siteFunctor p e).op.obj U)),
        (d.hom.app M).hom.app U x = x := by
  refine ⟨directComparisonAux A p e, ?_, ?_⟩
  · intro M U x
    rfl
  · intro d hd
    apply Iso.ext
    ext M U x
    exact hd M U x

/-- The identity-on-sections comparison determined by its uniqueness theorem.
Source: Stacks 03D1 (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
def directComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) :=
  (directComparison_existsUnique A p e).choose

/-- The inverse-image comparison is the unique mate of the identity-on-sections map.
This unit equation excludes any scalar automorphism in the comparison.
Source: Stacks 03D3, Categories 0B65
(blueprint: lem-sfb-etale-proetale-ringed-square-realization).
Proof: apply the constant-section module equivalence to the fixed-A adjunction.
The direct comparison identifies its right adjoint with the actual ringed direct
image. Uniqueness of adjoints gives the isomorphism below, with exactly the displayed
unit equation. In tensor terms it sends 1 tensor m to m; its inverse is insertion of 1.
Balancing gives the two inverse identities and shows that this is the ringed pullback. -/
theorem pullComparison_existsUnique (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) :
    ∃! b : modulePull A p e ⋙ restriction A X Y (toCorner e) ≅
        restriction A X Y (fromCorner e) ⋙ fixedPull A p e,
      ∀ M : Modules A X Y (fromCorner e),
        (fixedAdj A p e).unit.app ((restriction A X Y (fromCorner e)).obj M) ≫
            (fixedPush A p e).map (b.inv.app M) =
          (restriction A X Y (fromCorner e)).map ((moduleAdj A p e).unit.app M) ≫
            (directComparison A p e).hom.app ((modulePull A p e).obj M) := by
  let α := ((mateEquiv (moduleAdj A p e) (fixedAdj A p e)).symm
    (directComparison A p e).hom).natTrans
  have : IsIso α := isIso_inverseMate_of_equivalences
    (moduleAdj A p e) (fixedAdj A p e) (directComparison A p e)
  refine ⟨(asIso α).symm, ?_, ?_⟩
  · intro M
    exact (unit_mateEquiv_symm (moduleAdj A p e) (fixedAdj A p e)
      (directComparison A p e).hom M).symm
  · intro b hb
    apply Iso.ext_inv
    apply NatTrans.ext
    funext M
    apply ((fixedAdj A p e).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, hb]
    exact (unit_mateEquiv_symm (moduleAdj A p e) (fixedAdj A p e)
      (directComparison A p e).hom M)

/-- The specified unit-normalized identification of the two module pullbacks.
Source: Stacks 03D3 (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
def pullComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) :=
  (pullComparison_existsUnique A p e).choose

/-- The ringed square's direct-image comparison is the identity on base-changed sections.
Source: Stacks 09A5, 03D1
(blueprint: lem-sfb-etale-proetale-ringed-square-realization).
Proof: both composites evaluate on W as N(X times_Y W), with the same restriction
maps. The structural ring equation makes the identity on sections linear.
Identity maps give its inverse and naturality; faithful forgetting gives uniqueness. -/
theorem squareDirectComparison_existsUnique (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    ∃! d : modulePush A p .proetale ⋙ modulePush A p .comparisonY ≅
        modulePush A p .comparisonX ⋙ modulePush A p .etale,
      ∀ (M : Modules A X Y .xPro) (U : Y.Etaleᵒᵖ)
        (x : M.val.obj ((siteFunctor p .proetale).op.obj
          ((siteFunctor p .comparisonY).op.obj U))),
        (d.hom.app M).val.app U x = x := by
  let := restrictionIsEquivalence A X Y .yEt
  let l : (modulePush A p .proetale ⋙ modulePush A p .comparisonY) ⋙
      restriction A X Y .yEt ≅ restriction A X Y .xPro ⋙
        (fixedPush A p .proetale ⋙ fixedPush A p .comparisonY) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (directComparisonAux A p .comparisonY) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (directComparisonAux A p .proetale) _ ≪≫
      Functor.associator _ _ _
  let r : (modulePush A p .comparisonX ⋙ modulePush A p .etale) ⋙
      restriction A X Y .yEt ≅ restriction A X Y .xPro ⋙
        (fixedPush A p .comparisonX ⋙ fixedPush A p .etale) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (directComparisonAux A p .etale) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (directComparisonAux A p .comparisonX) _ ≪≫
      Functor.associator _ _ _
  let q := l ≪≫ Functor.isoWhiskerLeft (restriction A X Y .xPro)
    (supportSiteComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} A) p) ≪≫ r.symm
  let d := Functor.fullyFaithfulCancelRight (restriction A X Y .yEt) q
  refine ⟨d, ?_, ?_⟩
  · intro M U x
    have hh := congrArg (fun f ↦ f.hom.app U x)
      ((restriction A X Y .yEt).map_preimage (q.hom.app M))
    change (d.hom.app M).val.app U x = (q.hom.app M).hom.app U x at hh
    erw [hh]
    simp only [Functor.comp_obj, Iso.trans_assoc, directComparisonAux,
      supportSiteComparisonCoefficientDirectImageIso, supportSiteComparisonSiteBaseChangeIso,
      Functor.isoWhiskerLeft_trans, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.sheafPushforwardContinuousIso_hom, Iso.refl_inv, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_inv, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.whiskerLeft_app, NatIso.ofComponents_hom_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, NatIso.ofComponents_inv_app, Category.comp_id,
      Category.id_comp, ObjectProperty.FullSubcategory.comp_hom,
      Functor.sheafPushforwardContinuous_map_hom,
      Functor.sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj,
      ObjectProperty.FullSubcategory.id_hom, Functor.op_obj,
      Functor.sheafPushforwardContinuousComp_hom_app_hom_app, NatTrans.op_app,
      NatTrans.id_app, Functor.sheafPushforwardContinuousComp_inv_app_hom_app,
      ModuleCat.hom_comp, ConcreteCategory.hom_ofHom, LinearMap.comp_id_moduleCat,
      LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, id_eq, q, r, l]
    change (((restriction A X Y .xPro).obj M).obj.map (𝟙 _)) x = x
    erw [CategoryTheory.Functor.map_id]
    rfl
  · intro d' hd'
    apply Iso.ext
    ext M U x
    have hh := congrArg (fun f ↦ f.hom.app U x)
      ((restriction A X Y .yEt).map_preimage (q.hom.app M))
    change (d.hom.app M).val.app U x = (q.hom.app M).hom.app U x at hh
    erw [hh, hd' M U x]
    simp only [Functor.comp_obj, Iso.trans_assoc, directComparisonAux,
      supportSiteComparisonCoefficientDirectImageIso, supportSiteComparisonSiteBaseChangeIso,
      Functor.isoWhiskerLeft_trans, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.sheafPushforwardContinuousIso_hom, Iso.refl_inv, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_inv, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.whiskerLeft_app, NatIso.ofComponents_hom_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, NatIso.ofComponents_inv_app, Category.comp_id,
      Category.id_comp, ObjectProperty.FullSubcategory.comp_hom,
      Functor.sheafPushforwardContinuous_map_hom,
      Functor.sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj,
      ObjectProperty.FullSubcategory.id_hom, Functor.op_obj,
      Functor.sheafPushforwardContinuousComp_hom_app_hom_app, NatTrans.op_app,
      NatTrans.id_app, Functor.sheafPushforwardContinuousComp_inv_app_hom_app,
      ModuleCat.hom_comp, ConcreteCategory.hom_ofHom, LinearMap.comp_id_moduleCat,
      LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, id_eq, q, r, l]
    change x = (((restriction A X Y .xPro).obj M).obj.map (𝟙 _)) x
    erw [CategoryTheory.Functor.map_id]
    rfl

/-- The uniquely normalized ringed direct-image square.
Source: Stacks 09A5 (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
def squareDirectComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :=
  (squareDirectComparison_existsUnique A p).choose

/-- The ordinary ringed module square, defined as the actual adjunction mate.
Source: Stacks 09A5, 03D3 (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
def moduleSquare (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    modulePull A p .etale ⋙ modulePull A p .comparisonX ≅
      modulePull A p .comparisonY ⋙ modulePull A p .proetale :=
  ((conjugateIsoEquiv
    ((moduleAdj A p .etale).comp (moduleAdj A p .comparisonX))
    ((moduleAdj A p .comparisonY).comp (moduleAdj A p .proetale))).symm
      (squareDirectComparison A p).symm).symm

private theorem pullComparison_mate (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) :
    mateEquiv (moduleAdj A p e) (fixedAdj A p e) (pullComparison A p e).inv =
      (directComparison A p e).hom := by
  apply (mateEquiv (moduleAdj A p e) (fixedAdj A p e)).symm.injective
  apply NatTrans.ext
  funext M
  apply ((fixedAdj A p e).homEquiv _ _).injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_unit]
  exact ((pullComparison_existsUnique A p e).choose_spec.1 M).trans
    (unit_mateEquiv_symm (moduleAdj A p e) (fixedAdj A p e)
      (directComparison A p e).hom M)

private theorem directComparison_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) :
    directComparison A p e = directComparisonAux A p e := by
  apply Iso.ext
  ext M U x
  exact (directComparison_existsUnique A p e).choose_spec.1 M U x

/-- The ringed module comparison is the specified fixed-A comparison under the
constant-section equivalences, as an equality of the actual natural maps.
In particular its components preserve zero, addition and every A-action, since
the comparison on the right is a morphism of ModuleCat-valued sheaves.
Source: Stacks 09A5, 00YV, 03D3
(blueprint: lem-sfb-etale-proetale-ringed-square-realization).
Proof: under the tensor identifications, insertion of 1 becomes the identity on the
underlying inverse image. Naturality of the geometric square with zero, addition
and scalar endomorphisms makes the comparison A-linear. On right adjoints both
specified comparisons are the identity on the sections of the same base change.
The pullComparison unit equations and uniqueness of adjunction mates identify their
left-adjoint maps. This is equality of the specified maps, not just an isomorphism
between their endpoints. -/
theorem ordinary (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (M : Modules A X Y .yEt) :
    (restriction A X Y .xPro).map ((moduleSquare A p).hom.app M) ≫
        (pullComparison A p .proetale).hom.app ((modulePull A p .comparisonY).obj M) ≫
          (fixedPull A p .proetale).map ((pullComparison A p .comparisonY).hom.app M) =
      (pullComparison A p .comparisonX).hom.app ((modulePull A p .etale).obj M) ≫
        (fixedPull A p .comparisonX).map ((pullComparison A p .etale).hom.app M) ≫
          (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) p).hom.app
            ((restriction A X Y .yEt).obj M) := by
  let am₁ := (moduleAdj A p .etale).comp (moduleAdj A p .comparisonX)
  let am₂ := (moduleAdj A p .comparisonY).comp (moduleAdj A p .proetale)
  let af₁ := (fixedAdj A p .etale).comp (fixedAdj A p .comparisonX)
  let af₂ := (fixedAdj A p .comparisonY).comp (fixedAdj A p .proetale)
  let α₁ := TwoSquare.vComp (pullComparison A p .etale).inv
    (pullComparison A p .comparisonX).inv
  let α₂ := TwoSquare.vComp (pullComparison A p .comparisonY).inv
    (pullComparison A p .proetale).inv
  have hm₁ : mateEquiv am₁ af₁ α₁ =
      TwoSquare.hComp (directComparison A p .comparisonX).hom
        (directComparison A p .etale).hom := by
    erw [mateEquiv_hcomp]
    erw [pullComparison_mate, pullComparison_mate]
  have hm₂ : mateEquiv am₂ af₂ α₂ =
      TwoSquare.hComp (directComparison A p .proetale).hom
        (directComparison A p .comparisonY).hom := by
    erw [mateEquiv_hcomp]
    erw [pullComparison_mate, pullComparison_mate]
  have hc₁ : conjugateEquiv am₂ am₁ (moduleSquare A p).hom =
      (squareDirectComparison A p).hom := by
    exact (conjugateEquiv am₂ am₁).apply_symm_apply _
  have hc₂ : conjugateEquiv af₂ af₁
      (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) p).hom =
      (supportSiteComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} A) p).hom := by
    exact (conjugateEquiv af₂ af₁).apply_symm_apply _
  have he : α₁.whiskerLeft (moduleSquare A p).hom =
      α₂.whiskerRight
        (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) p).hom := by
    apply (mateEquiv am₂ af₁).injective
    refine (conjugateEquiv_mateEquiv_vcomp am₂ am₁ af₁
      (moduleSquare A p).hom α₁).trans ?_
    refine Eq.trans ?_ (mateEquiv_conjugateEquiv_vcomp am₂ af₂ af₁ α₂
      (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) p).hom).symm
    have hleft := congrArg₂ (fun a b ↦ a.whiskerTop b) hm₁ hc₁
    have hright := congrArg₂ (fun a b ↦ a.whiskerBottom b) hm₂ hc₂
    refine hleft.trans (Eq.trans ?_ hright.symm)
    ext N U x
    dsimp only [fromCorner, toCorner] at *
    simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, directComparison_eq]
    have hs := (squareDirectComparison_existsUnique A p).choose_spec.1 N U x
    dsimp only [directComparisonAux, NatIso.ofComponents_hom_app,
      ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      Functor.sheafPushforwardContinuous_map_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app] at *
    erw [coefficientDirectImage_hom_app]
    change ((squareDirectComparison A p).hom.app N).val.app U x = x
    exact hs
  have hx := congrArg (fun t ↦ t.natTrans.app M) he
  dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, α₁, α₂,
    TwoSquare.vComp, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app] at hx
  dsimp only [TwoSquare.natTrans] at hx
  simp only [Category.id_comp, Category.comp_id] at hx
  apply (cancel_epi ((fixedPull A p .comparisonX).map
    ((pullComparison A p .etale).inv.app M) ≫
      (pullComparison A p .comparisonX).inv.app ((modulePull A p .etale).obj M))).mp
  dsimp only [fromCorner, toCorner] at hx
  simp only [Category.assoc]
  erw [reassoc_of% hx]
  simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

/-- Exactness of the fixed-A pullbacks: these are the published exact inverse images.
Source: Stacks 00YV (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
instance fixedPullAdditive (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) : (fixedPull A p e).Additive := by
  cases e with
  | etale =>
    exact inferInstanceAs ((Etale.upperStar (ModuleCat.{u + 1} A) p).Additive)
  | proetale =>
    exact inferInstanceAs ((upperStar (ModuleCat.{u + 1} A) p).Additive)
  | comparisonX =>
    exact inferInstanceAs ((comparisonUpperStar (ModuleCat.{u + 1} A) X).Additive)
  | comparisonY =>
    exact inferInstanceAs ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).Additive)

/-- Left exactness of the published fixed-A inverse images.
Source: Stacks 00YV (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
instance fixedPullLimits (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) :
    PreservesFiniteLimits (fixedPull A p e) := by
  cases e with
  | etale =>
    exact inferInstanceAs (PreservesFiniteLimits (Etale.upperStar (ModuleCat.{u + 1} A) p))
  | proetale =>
    exact inferInstanceAs (PreservesFiniteLimits (upperStar (ModuleCat.{u + 1} A) p))
  | comparisonX =>
    exact inferInstanceAs (PreservesFiniteLimits (comparisonUpperStar (ModuleCat.{u + 1} A) X))
  | comparisonY =>
    exact inferInstanceAs (PreservesFiniteLimits (comparisonUpperStar (ModuleCat.{u + 1} A) Y))

/-- Right exactness of the published fixed-A inverse images.
Source: Stacks 00YV (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
instance fixedPullColimits (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) :
    PreservesFiniteColimits (fixedPull A p e) := by
  cases e with
  | etale =>
    exact inferInstanceAs (PreservesFiniteColimits (Etale.upperStar (ModuleCat.{u + 1} A) p))
  | proetale =>
    exact inferInstanceAs (PreservesFiniteColimits (upperStar (ModuleCat.{u + 1} A) p))
  | comparisonX =>
    exact inferInstanceAs (PreservesFiniteColimits (comparisonUpperStar (ModuleCat.{u + 1} A) X))
  | comparisonY =>
    exact inferInstanceAs (PreservesFiniteColimits (comparisonUpperStar (ModuleCat.{u + 1} A) Y))

/-- The actual ringed pullbacks are additive under the constant-section identifications.
Source: Stacks 00YV, 03D2 (blueprint: lem-sfb-etale-proetale-ringed-square-realization).
Proof: pullComparison identifies each pullback, through additive equivalences, with
the original fixed-A inverse image. Faithfulness reflects preservation of addition. -/
theorem modulePullAdditive (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) : (modulePull A p e).Additive := by
  have : (restriction A X Y (fromCorner e) ⋙ fixedPull A p e).Additive :=
    inferInstance
  have : (modulePull A p e ⋙ restriction A X Y (toCorner e)).Additive :=
    Functor.additive_of_iso (pullComparison A p e).symm
  exact Functor.additive_of_comp_faithful _ (restriction A X Y (toCorner e))

/-- The actual ringed pullbacks are left exact with their identified constant coefficients.
Source: Stacks 00YV, 03D2 (blueprint: lem-sfb-etale-proetale-ringed-square-realization).
Proof: pullComparison and the constant-ring equivalences transport finite-limit
preservation from the exact fixed-A inverse image to the actual module pullback. -/
theorem modulePullLimits (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) :
    PreservesFiniteLimits (modulePull A p e) := by
  have : PreservesFiniteLimits
      (modulePull A p e ⋙ restriction A X Y (toCorner e)) :=
    preservesFiniteLimits_of_natIso (pullComparison A p e).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (restriction A X Y (toCorner e))

/-- The actual ringed pullbacks are right exact with their identified constant coefficients.
Source: Stacks 00YV, 03D2 (blueprint: lem-sfb-etale-proetale-ringed-square-realization).
Proof: the module pullback is left adjoint to the actual direct image, hence preserves
colimits. Equivalently transport finite colimits through pullComparison. -/
theorem modulePullColimits (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Edge) :
    PreservesFiniteColimits (modulePull A p e) := by
  have : PreservesColimitsOfSize.{0, 0} (modulePull A p e) :=
    (moduleAdj A p e).leftAdjoint_preservesColimits
  infer_instance

attribute [instance] modulePullAdditive modulePullLimits modulePullColimits

section Derived

variable (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}} (p : X ⟶ Y)
variable [∀ c : Corner, HasDerivedCategory.{w} (Modules A X Y c)]
variable [∀ c : Corner, HasDerivedCategory.{w} (Fixed A X Y c)]

/-- Exact localization of the existing constant-section equivalence.
Source: Stacks 015F (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
def derivedRestriction (c : Corner) :
    DerivedCategory (Modules A X Y c) ⥤ DerivedCategory (Fixed A X Y c) :=
  letI := restrictionAdditive A X Y c
  letI := restrictionIsEquivalence A X Y c
  (restriction A X Y c).mapDerivedCategory

/-- Exact termwise localization of the actual module pullback.
Source: Stacks 015F (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
def derivedModulePull (e : Edge) :
    DerivedCategory (Modules A X Y (fromCorner e)) ⥤
      DerivedCategory (Modules A X Y (toCorner e)) :=
  letI := modulePullAdditive A p e
  letI := modulePullLimits A p e
  letI := modulePullColimits A p e
  (modulePull A p e).mapDerivedCategory

/-- Exact termwise localization of the published fixed-A pullback.
Source: Stacks 015F (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
def derivedFixedPull (e : Edge) :
    DerivedCategory (Fixed A X Y (fromCorner e)) ⥤
      DerivedCategory (Fixed A X Y (toCorner e)) :=
  letI := fixedPullAdditive A p e
  letI := fixedPullLimits A p e
  letI := fixedPullColimits A p e
  (fixedPull A p e).mapDerivedCategory

/-- Exact localization of the unit-normalized constant-ring pullback identification.
Source: Stacks 015F (blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
def derivedPullComparison (e : Edge) :
    (derivedModulePull A p e) ⋙
        (derivedRestriction A (X := X) (Y := Y) (toCorner e)) ≅
      (derivedRestriction A (X := X) (Y := Y) (fromCorner e)) ⋙
        (derivedFixedPull A p e) :=
  letI := modulePullAdditive A p e
  letI := modulePullLimits A p e
  letI := modulePullColimits A p e
  letI := restrictionAdditive A X Y (toCorner e)
  letI := restrictionAdditive A X Y (fromCorner e)
  letI := restrictionIsEquivalence A X Y (toCorner e)
  letI := restrictionIsEquivalence A X Y (fromCorner e)
  letI := fixedPullAdditive A p e
  letI := fixedPullLimits A p e
  letI := fixedPullColimits A p e
  Functor.mapDerivedCategorySquareIso
    (F₁ := modulePull A p e) (F₂ := restriction A X Y (toCorner e))
    (G₁ := restriction A X Y (fromCorner e)) (G₂ := fixedPull A p e)
    (pullComparison A p e)

/-- The ordinary uncompleted ringed derived comparison in the exchange orientation.
It is obtained by applying the exact termwise localization to the inverse ringed module
square, with the canonical derived-composition factorization isomorphisms.
Source: Stacks 015F, 09A5
(blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
def theta :
    (derivedModulePull A p .comparisonY) ⋙
        (derivedModulePull A p .proetale) ≅
      (derivedModulePull A p .etale) ⋙
        (derivedModulePull A p .comparisonX) :=
  letI := modulePullAdditive A p .etale
  letI := modulePullLimits A p .etale
  letI := modulePullColimits A p .etale
  letI := modulePullAdditive A p .proetale
  letI := modulePullLimits A p .proetale
  letI := modulePullColimits A p .proetale
  letI := modulePullAdditive A p .comparisonX
  letI := modulePullLimits A p .comparisonX
  letI := modulePullColimits A p .comparisonX
  letI := modulePullAdditive A p .comparisonY
  letI := modulePullLimits A p .comparisonY
  letI := modulePullColimits A p .comparisonY
  Functor.mapDerivedCategorySquareIso
    (F₁ := modulePull A p .comparisonY) (F₂ := modulePull A p .proetale)
    (G₁ := modulePull A p .etale) (G₂ := modulePull A p .comparisonX)
    (moduleSquare A p).symm

/-- The a of the node: termwise localization of the recorded fixed-A comparison.
No bounded-below inclusion or completed category occurs here.
Source: Stacks 015F, 09A5
(blueprint: lem-sfb-etale-proetale-ringed-square-realization). -/
def a :
    (derivedFixedPull A p .etale) ⋙
        (derivedFixedPull A p .comparisonX) ≅
      (derivedFixedPull A p .comparisonY) ⋙
        (derivedFixedPull A p .proetale) :=
  letI := fixedPullAdditive A p .etale
  letI := fixedPullLimits A p .etale
  letI := fixedPullColimits A p .etale
  letI := fixedPullAdditive A p .proetale
  letI := fixedPullLimits A p .proetale
  letI := fixedPullColimits A p .proetale
  letI := fixedPullAdditive A p .comparisonX
  letI := fixedPullLimits A p .comparisonX
  letI := fixedPullColimits A p .comparisonX
  letI := fixedPullAdditive A p .comparisonY
  letI := fixedPullLimits A p .comparisonY
  letI := fixedPullColimits A p .comparisonY
  Functor.mapDerivedCategorySquareIso
    (F₁ := fixedPull A p .etale) (F₂ := fixedPull A p .comparisonX)
    (G₁ := fixedPull A p .comparisonY) (G₂ := fixedPull A p .proetale)
    (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) p)

end Derived

private theorem pasteSquare
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X₀ X₁ Y₀ Y₁ : C} {A₀ A₁ B₀ B₁ : D}
    (e₀ : X₀ ≅ X₁) (e₁ : Y₀ ≅ Y₁) (c : X₀ ≅ Y₀)
    (f₀ : A₀ ≅ A₁) (f₁ : B₀ ≅ B₁) (d : A₀ ≅ B₀)
    (q : F.obj X₀ ⟶ A₀) (a : F.obj X₁ ⟶ A₁) (b : F.obj Y₁ ⟶ B₁)
    (h₀ : F.map e₀.hom ≫ a = q ≫ f₀.hom)
    (h₁ : F.map (c.hom ≫ e₁.hom) ≫ b = q ≫ d.hom ≫ f₁.hom) :
    F.map (e₀.inv ≫ c.hom ≫ e₁.hom) ≫ b = a ≫ f₀.inv ≫ d.hom ≫ f₁.hom := by
  apply (cancel_epi (F.map e₀.hom)).mp
  simp only [← F.map_comp_assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% h₀]
  simp only [Iso.hom_inv_id_assoc]
  exact h₁

private theorem invertSquare
    {B C D : Type*} [Category B] [Category C] [Category D] (F : C ⥤ D)
    {P Q : B ⥤ C} {S T : B ⥤ D} (s : P ≅ Q) (t : S ≅ T) (K : B)
    {Z W : D} (a₁ : F.obj (P.obj K) ⟶ Z) (a₂ : Z ⟶ S.obj K)
    (b₁ : F.obj (Q.obj K) ⟶ W) (b₂ : W ⟶ T.obj K)
    (h : F.map (s.hom.app K) ≫ b₁ ≫ b₂ = a₁ ≫ a₂ ≫ t.hom.app K) :
    F.map (s.inv.app K) ≫ a₁ ≫ a₂ = b₁ ≫ b₂ ≫ t.inv.app K := by
  have hh := congrArg (fun f ↦ F.map (s.inv.app K) ≫ f ≫ t.inv.app K) h
  simpa only [Category.assoc, ← F.map_comp_assoc, Iso.inv_hom_id_app,
    F.map_id, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id] using hh.symm

/-- The ringed derived comparison theta is exactly a inverse under the specified
constant-section equivalences. The equation is an equality of components for every
object of the entire uncompleted derived category; by naturality it is the equality
of the specified natural isomorphisms. Both sides have the same source and target
through the four derivedPullComparison identifications.

Source: Stacks 09A5, square preceding 09A6; Derived Categories 015F
(blueprint: lem-sfb-etale-proetale-ringed-square-realization).

Proof: ordinary identifies the actual module mate with the recorded fixed-A comparison.
The four inverse images are exact, so their termwise functors compute their ordinary
left derived functors even on unbounded complexes. Naturality makes the comparison
in every degree a chain isomorphism. Localization preserves inverses and compositions;
its universal property says equality of the descended transformations can be checked
after precomposition with Q. Apply it to the inverse of the ordinary equality and
insert the exact-derived composition identifications. This gives theta = a inverse
with the displayed edge identifications, on all derived objects and maps. -/
theorem derived (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    [∀ c : Corner, HasDerivedCategory.{w} (Modules A X Y c)]
    [∀ c : Corner, HasDerivedCategory.{w} (Fixed A X Y c)]
    (K : DerivedCategory (Modules A X Y .yEt)) :
    (derivedRestriction A (X := X) (Y := Y) .xPro).map ((theta A p).hom.app K) ≫
        (derivedPullComparison A p .comparisonX).hom.app
          ((derivedModulePull A p .etale).obj K) ≫
        (derivedFixedPull A p .comparisonX).map
          ((derivedPullComparison A p .etale).hom.app K) =
      (derivedPullComparison A p .proetale).hom.app
          ((derivedModulePull A p .comparisonY).obj K) ≫
        (derivedFixedPull A p .proetale).map
          ((derivedPullComparison A p .comparisonY).hom.app K) ≫
        (a A p).inv.app ((derivedRestriction A (X := X) (Y := Y) .yEt).obj K) := by
  let me : Modules A X Y .yEt ⥤ Modules A X Y .xEt := modulePull A p .etale
  let mx : Modules A X Y .xEt ⥤ Modules A X Y .xPro := modulePull A p .comparisonX
  let my : Modules A X Y .yEt ⥤ Modules A X Y .yPro := modulePull A p .comparisonY
  let mp : Modules A X Y .yPro ⥤ Modules A X Y .xPro := modulePull A p .proetale
  let fe : Fixed A X Y .yEt ⥤ Fixed A X Y .xEt := fixedPull A p .etale
  let fx : Fixed A X Y .xEt ⥤ Fixed A X Y .xPro := fixedPull A p .comparisonX
  let fy : Fixed A X Y .yEt ⥤ Fixed A X Y .yPro := fixedPull A p .comparisonY
  let fp : Fixed A X Y .yPro ⥤ Fixed A X Y .xPro := fixedPull A p .proetale
  let ry := restriction A X Y .yEt
  let rx := restriction A X Y .xEt
  let rp := restriction A X Y .yPro
  let rs := restriction A X Y .xPro
  let : me.Additive := modulePullAdditive A p .etale
  let : PreservesFiniteLimits me := modulePullLimits A p .etale
  let : PreservesFiniteColimits me := modulePullColimits A p .etale
  let : mx.Additive := modulePullAdditive A p .comparisonX
  let : PreservesFiniteLimits mx := modulePullLimits A p .comparisonX
  let : PreservesFiniteColimits mx := modulePullColimits A p .comparisonX
  let : my.Additive := modulePullAdditive A p .comparisonY
  let : PreservesFiniteLimits my := modulePullLimits A p .comparisonY
  let : PreservesFiniteColimits my := modulePullColimits A p .comparisonY
  let : mp.Additive := modulePullAdditive A p .proetale
  let : PreservesFiniteLimits mp := modulePullLimits A p .proetale
  let : PreservesFiniteColimits mp := modulePullColimits A p .proetale
  let : fe.Additive := fixedPullAdditive A p .etale
  let : PreservesFiniteLimits fe := fixedPullLimits A p .etale
  let : PreservesFiniteColimits fe := fixedPullColimits A p .etale
  let : fx.Additive := fixedPullAdditive A p .comparisonX
  let : PreservesFiniteLimits fx := fixedPullLimits A p .comparisonX
  let : PreservesFiniteColimits fx := fixedPullColimits A p .comparisonX
  let : fy.Additive := fixedPullAdditive A p .comparisonY
  let : PreservesFiniteLimits fy := fixedPullLimits A p .comparisonY
  let : PreservesFiniteColimits fy := fixedPullColimits A p .comparisonY
  let : fp.Additive := fixedPullAdditive A p .proetale
  let : PreservesFiniteLimits fp := fixedPullLimits A p .proetale
  let : PreservesFiniteColimits fp := fixedPullColimits A p .proetale
  let : ry.Additive := restrictionAdditive A X Y .yEt
  let : ry.IsEquivalence := restrictionIsEquivalence A X Y .yEt
  let : rx.Additive := restrictionAdditive A X Y .xEt
  let : rx.IsEquivalence := restrictionIsEquivalence A X Y .xEt
  let : rp.Additive := restrictionAdditive A X Y .yPro
  let : rp.IsEquivalence := restrictionIsEquivalence A X Y .yPro
  let : rs.Additive := restrictionAdditive A X Y .xPro
  let : rs.IsEquivalence := restrictionIsEquivalence A X Y .xPro
  let be : me ⋙ rx ≅ ry ⋙ fe := pullComparison A p .etale
  let bx : mx ⋙ rs ≅ rx ⋙ fx := pullComparison A p .comparisonX
  let byy : my ⋙ rp ≅ ry ⋙ fy := pullComparison A p .comparisonY
  let bp : mp ⋙ rs ≅ rp ⋙ fp := pullComparison A p .proetale
  let q : (me ⋙ mx) ⋙ rs ≅ ry ⋙ (fe ⋙ fx) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft me bx ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight be fx ≪≫
        Functor.associator _ _ _
  have hq (M : Modules A X Y .yEt) :
      rs.map ((moduleSquare A p).hom.app M) ≫ bp.hom.app (my.obj M) ≫
        fp.map (byy.hom.app M) = q.hom.app M ≫
          (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) p).hom.app
            (ry.obj M) := by
    simpa only [q, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Iso.symm_hom, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using ordinary A p M
  let : PreservesFiniteLimits (me ⋙ mx) := comp_preservesFiniteLimits me mx
  let : PreservesFiniteColimits (me ⋙ mx) := comp_preservesFiniteColimits me mx
  let : PreservesFiniteLimits (fe ⋙ fx) := comp_preservesFiniteLimits fe fx
  let : PreservesFiniteColimits (fe ⋙ fx) := comp_preservesFiniteColimits fe fx
  have he := Functor.mapDerivedCategorySquareIso_comp.{_, _, _, _, _, _, _, _, _, _, _, _,
    w, w, w, w, w, w} me mx (me ⋙ mx)
    fe fx (fe ⋙ fx) ry rx rs be bx q (Iso.refl _) (Iso.refl _)
    (fun M ↦ by
      simp only [q, Iso.trans_hom, Iso.refl_hom, NatTrans.id_app,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_hom_app, Iso.symm_hom, Functor.associator_inv_app,
        Category.id_comp, Category.comp_id, Category.assoc]
      erw [CategoryTheory.Functor.map_id, Category.id_comp])
  have hp := Functor.mapDerivedCategorySquareIso_comp.{_, _, _, _, _, _, _, _, _, _, _, _,
    w, w, w, w, w, w} my mp (me ⋙ mx)
    fy fp (fe ⋙ fx) ry rp rs byy bp q (moduleSquare A p)
    (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) p) hq
  let cf : fe ⋙ fx ≅ fy ⋙ fp :=
    supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) p
  let sm : (me).mapDerivedCategory.{w, w} ⋙
      (mx).mapDerivedCategory.{w, w} ≅
    (my).mapDerivedCategory.{w, w} ⋙ (mp).mapDerivedCategory.{w, w} :=
      Functor.mapDerivedCategorySquareIso (moduleSquare A p)
  let sf : (fe).mapDerivedCategory.{w, w} ⋙
      (fx).mapDerivedCategory.{w, w} ≅
    (fy).mapDerivedCategory.{w, w} ⋙ (fp).mapDerivedCategory.{w, w} :=
      Functor.mapDerivedCategorySquareIso
    (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) p)
  have hf : rs.mapDerivedCategory.{w, w}.map (sm.hom.app K) ≫
      (Functor.mapDerivedCategorySquareIso bp).hom.app (my.mapDerivedCategory.{w, w}.obj K) ≫
      fp.mapDerivedCategory.{w, w}.map ((Functor.mapDerivedCategorySquareIso byy).hom.app K) =
    (Functor.mapDerivedCategorySquareIso bx).hom.app (me.mapDerivedCategory.{w, w}.obj K) ≫
      fx.mapDerivedCategory.{w, w}.map ((Functor.mapDerivedCategorySquareIso be).hom.app K) ≫
      sf.hom.app (ry.mapDerivedCategory.{w, w}.obj K) := by
    let de := Functor.mapDerivedCategoryCompIso me mx
    let dp := Functor.mapDerivedCategoryCompIso my mp
    let ce := Functor.mapDerivedCategoryCompIso fe fx
    let cp := Functor.mapDerivedCategoryCompIso fy fp
    let bxe := (Functor.mapDerivedCategorySquareIso bx).hom.app
      (me.mapDerivedCategory.{w, w}.obj K) ≫
      fx.mapDerivedCategory.{w, w}.map ((Functor.mapDerivedCategorySquareIso be).hom.app K)
    let bpy := (Functor.mapDerivedCategorySquareIso bp).hom.app
      (my.mapDerivedCategory.{w, w}.obj K) ≫
      fp.mapDerivedCategory.{w, w}.map ((Functor.mapDerivedCategorySquareIso byy).hom.app K)
    have heK := congrArg (fun i ↦ i.hom.app K) he
    have hpK := congrArg (fun i ↦ i.hom.app K) hp
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id] at heK hpK
    change rs.mapDerivedCategory.{w, w}.map
        (((Functor.mapDerivedCategoryNatIso (Iso.refl (me ⋙ mx))).hom.app K) ≫
          de.hom.app K) ≫ bxe =
      (Functor.mapDerivedCategorySquareIso q).hom.app K ≫
        ((Functor.mapDerivedCategoryNatIso (Iso.refl (fe ⋙ fx))).hom.app
          (ry.mapDerivedCategory.{w, w}.obj K) ≫
            ce.hom.app (ry.mapDerivedCategory.{w, w}.obj K)) at heK
    have hid : (Functor.mapDerivedCategoryNatIso (Iso.refl (fe ⋙ fx))).hom.app
        (ry.mapDerivedCategory.{w, w}.obj K) = 𝟙 _ :=
      congrArg (fun t ↦ t.app (ry.mapDerivedCategory.{w, w}.obj K))
        (Functor.mapDerivedCategoryNatIso_refl (F := fe ⋙ fx))
    have hid' : (Functor.mapDerivedCategoryNatIso (Iso.refl (me ⋙ mx))).hom.app K = 𝟙 _ :=
      congrArg (fun t ↦ t.app K) (Functor.mapDerivedCategoryNatIso_refl (F := me ⋙ mx))
    erw [hid, Category.id_comp, hid', Category.id_comp] at heK
    change rs.mapDerivedCategory.{w, w}.map
        ((Functor.mapDerivedCategoryNatIso (moduleSquare A p)).hom.app K ≫
          dp.hom.app K) ≫ bpy =
      (Functor.mapDerivedCategorySquareIso q).hom.app K ≫
        ((Functor.mapDerivedCategoryNatIso cf).hom.app
          (ry.mapDerivedCategory.{w, w}.obj K) ≫
            cp.hom.app (ry.mapDerivedCategory.{w, w}.obj K)) at hpK
    have hpaste := pasteSquare rs.mapDerivedCategory.{w, w}
      (de.app K) (dp.app K)
      ((Functor.mapDerivedCategoryNatIso (moduleSquare A p)).app K)
      (ce.app (ry.mapDerivedCategory.{w, w}.obj K))
      (cp.app (ry.mapDerivedCategory.{w, w}.obj K))
      ((Functor.mapDerivedCategoryNatIso cf).app
          (ry.mapDerivedCategory.{w, w}.obj K))
      ((Functor.mapDerivedCategorySquareIso q).hom.app K) bxe bpy heK hpK
    simpa only [sm, sf, bxe, bpy, de, dp, ce, cp, cf,
      Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Iso.app_hom, Iso.app_inv, Category.assoc] using hpaste
  have htheta : (theta A p).hom = sm.inv := by
    simp only [theta, sm, Functor.mapDerivedCategorySquareIso, Iso.trans_hom,
      Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
    rfl
  change rs.mapDerivedCategory.{w, w}.map ((theta A p).hom.app K) ≫
      (Functor.mapDerivedCategorySquareIso bx).hom.app (me.mapDerivedCategory.{w, w}.obj K) ≫
      fx.mapDerivedCategory.{w, w}.map ((Functor.mapDerivedCategorySquareIso be).hom.app K) =
    (Functor.mapDerivedCategorySquareIso bp).hom.app (my.mapDerivedCategory.{w, w}.obj K) ≫
      fp.mapDerivedCategory.{w, w}.map ((Functor.mapDerivedCategorySquareIso byy).hom.app K) ≫
      sf.inv.app (ry.mapDerivedCategory.{w, w}.obj K)
  rw [htheta]
  exact invertSquare rs.mapDerivedCategory.{w, w} sm
    (Functor.isoWhiskerLeft ry.mapDerivedCategory.{w, w} sf) K
    ((Functor.mapDerivedCategorySquareIso bx).hom.app
      (me.mapDerivedCategory.{w, w}.obj K))
    (fx.mapDerivedCategory.{w, w}.map ((Functor.mapDerivedCategorySquareIso be).hom.app K))
    ((Functor.mapDerivedCategorySquareIso bp).hom.app
      (my.mapDerivedCategory.{w, w}.obj K))
    (fp.mapDerivedCategory.{w, w}.map ((Functor.mapDerivedCategorySquareIso byy).hom.app K)) hf

end AlgebraicGeometry.ProEtale.SfbRingedSquare
