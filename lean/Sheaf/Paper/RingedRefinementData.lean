/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.RingedCoefficientProjectionCocycle
public import Sheaf.Paper.RingedProjectionRestriction
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.AlgebraicGeometry.ProperOpenSection


public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-!
# Coefficient change and clopen refinement mates

Source: Bhatt--Scholze 6.7.6--6.7.7, ordinary-derived coefficient supplement
(blueprint: lem-pur-ringed-refinement-coefficient-square).

All sites below are the original small pro-etale sites, or their vertical sequence
sites. Presentations use actual module sheaves and ordinary unbounded localizations.
Adjunctions and representative equations fix the operations; none of the refinement
or coefficient squares is an assumption.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option backward.isDefEq.respectTransparency true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.RingedRefinement

/-- Ring sheaves on the actual site; systems have all their horizontal restrictions.
Source: Stacks 09A5, 0941 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
abbrev Rings (m : Mode) (T : Scheme.{u}) :=
  Sheaf (topology m T) CommRingCat.{u + 1}

/-- Canonical inverse image of ring sheaves by Kan extension and sheafification.
Source: Stacks 00YV, 09A5 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def ringInverse (m : Mode) {U T : Scheme.{u}} (f : U ⟶ T) :
    Rings m T ⥤ Rings m U :=
  Functor.sheafPullbackConstruction.sheafPullback (baseChange m f)
    CommRingCat.{u + 1} (topology m T) (topology m U)

/-- Its specified sheaf adjunction, including the unit used for structural ring maps.
Source: Stacks 00YV, 09A5 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def ringAdjunction (m : Mode) {U T : Scheme.{u}} (f : U ⟶ T) :
    ringInverse m f ⊣ (baseChange m f).sheafPushforwardContinuous
      CommRingCat.{u + 1} (topology m T) (topology m U) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (baseChange m f)
    CommRingCat.{u + 1} (topology m T) (topology m U)

set_option backward.isDefEq.respectTransparency false in
/-- Canonical fibre-product associativity on the original sites.
Source: Stacks 09A5 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def siteTriangle (m : Mode) {T : Scheme.{u}} {U V : Over T} (f : U ⟶ V) :
    baseChange m U.hom ≅ baseChange m V.hom ⋙ baseChange m f.left := by
  have e : proEtaleBaseChange U.hom ≅
      proEtaleBaseChange V.hom ⋙ proEtaleBaseChange f.left :=
    MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
      f.left V.hom U.hom (Over.w f).symm
  cases m with
  | ordinary => exact e
  | systems => exact NatIso.prod (Iso.refl (𝟭 ℕ)) e

/-- Ring direct-image compositors fixed on every section by the fibre-product
associator. These are presentations of the canonical maps, never arbitrary maps.
Source: Stacks 03D7, 09A5 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
structure Coefficients (m : Mode) (T : Scheme.{u}) where
  directTriangle : ∀ {U V : Over T} (f : U ⟶ V),
    (baseChange m f.left).sheafPushforwardContinuous CommRingCat.{u + 1}
        (topology m V.left) (topology m U.left) ⋙
      (baseChange m V.hom).sheafPushforwardContinuous CommRingCat.{u + 1}
        (topology m T) (topology m V.left) ≅
      (baseChange m U.hom).sheafPushforwardContinuous CommRingCat.{u + 1}
        (topology m T) (topology m U.left)
  sections : ∀ {U V : Over T} (f : U ⟶ V) (R : Rings m U.left)
    (W : (Site m T)ᵒᵖ),
    ((directTriangle f).hom.app R).hom.app W =
      R.obj.map ((siteTriangle m f).hom.app W.unop).op

/-- The rings are literally inverse images of the ambient ring, on coefficients
and their homomorphisms. Source: Stacks 03D7
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def Coefficients.rings {m : Mode} {T : Scheme.{u}} (_c : Coefficients m T)
    (W : Over T) := ringInverse m W.hom

/-- The inverse-image identification is the conjugate of the section-normalized
ring direct-image compositor. Source: Stacks 03D7, 07A6
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def Coefficients.pull {m : Mode} {T : Scheme.{u}} (c : Coefficients m T)
    {U V : Over T} (f : U ⟶ V) :
    c.rings V ⋙ ringInverse m f.left ≅ c.rings U :=
  ((conjugateIsoEquiv ((ringAdjunction m V.hom).comp (ringAdjunction m f.left))
    (ringAdjunction m U.hom)).symm (c.directTriangle f)).symm

/-- The structural ring map is the adjoint of the inverse-image identification.
Source: Stacks 03D7 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def Coefficients.structural {m : Mode} {T : Scheme.{u}} (c : Coefficients m T)
    {U V : Over T} (f : U ⟶ V) (R : Rings m T) :
    (c.rings V).obj R ⟶ ((baseChange m f.left).sheafPushforwardContinuous
      CommRingCat.{u + 1} (topology m V.left) (topology m U.left)).obj ((c.rings U).obj R) :=
  (ringAdjunction m f.left).homEquiv _ _ ((c.pull f).hom.app R)

/-- Exact open extension adjoint to a specified module restriction. Its adjunction
fixes it up to the unique compatible isomorphism.
Source: Stacks 03DI (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
structure OpenModel {m : Mode} {U V : Scheme.{u}} (j : U ⟶ V)
    {R : Rings m V} {S : Rings m U} (e : Operation (baseChange m j) R S) where
  functor : Mod S ⥤ Mod R
  adjunction : functor ⊣ e.pullback
  [additive : functor.Additive]
  [limits : PreservesFiniteLimits functor]
  [colimits : PreservesFiniteColimits functor]
  unit : ∀ M, IsIso (adjunction.unit.app M)

attribute [instance] OpenModel.additive OpenModel.limits OpenModel.colimits

/-- The ringed operations are the dependency's actual module Kan extension,
sectionwise direct image and their canonical derived adjunctions. Open extension is
adjoint to that same restriction. Scalar extension is the recorded K-flat universal
pair. All these are conclusion data, not extra hypotheses on the rings or schemes.
Source: Stacks 03D7, 06YY, 07A6, 03DI
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
structure Calculus {m : Mode} {T : Scheme.{u}} (c : Coefficients m T) where
  operation : ∀ {U V : Over T} (f : U ⟶ V) (R : Rings m T),
    Operation (baseChange m f.left) ((c.rings V).obj R) ((c.rings U).obj R)
  coefficient : ∀ {U V : Over T} (f : U ⟶ V) (R : Rings m T),
    (operation f R).coefficient =
      ⟨Functor.whiskerRight (c.structural f R).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  openModel : ∀ {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left] (R : Rings m T),
    OpenModel j.left (operation j R)
  scalar : ∀ (W : Over T) {A B : Rings m T} (a : A ⟶ B),
    DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
      ((c.rings W).map a)

/-- Ordinary unbounded coefficient categories, using the dependency localization.
Source: Stacks 05RU (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
abbrev category {m : Mode} {T : Scheme.{u}} (c : Coefficients m T)
    (W : Over T) (R : Rings m T) := Der ((c.rings W).obj R)

/-- Termwise exact open extension on the actual derived category.
Source: Stacks 03DI (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def Calculus.shriek {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    (o : Calculus c) {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
    (R : Rings m T) := (o.openModel j R).functor.mapDerivedCategory

/-- The canonical exact-functor shift on open extension, kept behind its named
construction to avoid expanding localization proof data in every comparison.
Source: Stacks 015F, 03DI (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
instance Calculus.shriekShift {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    (o : Calculus c) {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
    (R : Rings m T) : (o.shriek j R).CommShift ℤ :=
  inferInstanceAs ((o.openModel j R).functor.mapDerivedCategory.CommShift ℤ)

/-- The localized normalized open adjunction.
Source: Stacks 03DI, 015F (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def Calculus.openAdjunction {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    (o : Calculus c) {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
    (R : Rings m T) : o.shriek j R ⊣ (o.operation j R).left :=
  exactDerivedAdjunction (o.openModel j R).adjunction

set_option backward.isDefEq.respectTransparency false in
/-- Site associativity for two arrows over the ambient scheme.
Source: Stacks 09A5 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def siteComp (m : Mode) {T : Scheme.{u}} {U V W : Over T}
    (f : U ⟶ V) (g : V ⟶ W) :
    baseChange m (f ≫ g).left ≅ baseChange m g.left ⋙ baseChange m f.left := by
  have e := MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
    f.left g.left
  cases m with
  | ordinary => exact e
  | systems => exact NatIso.prod (Iso.refl (𝟭 ℕ)) e

set_option backward.isDefEq.respectTransparency false in
/-- The actual identity fibre product on the site.
Source: Stacks 09A5 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def siteId (m : Mode) {T : Scheme.{u}} (W : Over T) :
    baseChange m (𝟙 W.left) ≅ 𝟭 (Site m W.left) := by
  have e := MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ W.left
  cases m with
  | ordinary => exact e
  | systems => exact NatIso.prod (Iso.refl (𝟭 ℕ)) e

/-- Direct-image compositors are fixed on all sections, and their conjugates
fix all inverse-image compositors. Source: Stacks 03D7, 0D6E
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
structure Spatial {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    (o : Calculus c) where
  comp : ∀ {U V W : Over T} (f : U ⟶ V) (g : V ⟶ W) (R : Rings m T),
    (o.operation f R).pushforward ⋙ (o.operation g R).pushforward ≅
      (o.operation (f ≫ g) R).pushforward
  comp_sections : ∀ {U V W : Over T} (f : U ⟶ V) (g : V ⟶ W) (R : Rings m T)
    (N : Mod ((c.rings U).obj R)) (Z : (Site m W.left)ᵒᵖ),
    HEq (((comp f g R).hom.app N).val.app Z).hom
      (N.val.map ((siteComp m f g).hom.app Z.unop).op).hom
  identity : ∀ (W : Over T) (R : Rings m T),
    (o.operation (𝟙 W) R).pushforward ≅ 𝟭 (Mod ((c.rings W).obj R))
  id_sections : ∀ (W : Over T) (R : Rings m T) (N : Mod ((c.rings W).obj R))
    (Z : (Site m W.left)ᵒᵖ),
    HEq (((identity W R).hom.app N).val.app Z).hom
      (N.val.map ((siteId m W).inv.app Z.unop).op).hom

/-- Ordinary pullback composition is the conjugate of sectionwise direct image.
Source: Stacks 07A6 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def Spatial.ordinaryComp {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (p : Spatial o) {U V W : Over T}
    (f : U ⟶ V) (g : V ⟶ W) (R : Rings m T) :
    (o.operation g R).pullback ⋙ (o.operation f R).pullback ≅
      (o.operation (f ≫ g) R).pullback :=
  ((conjugateIsoEquiv
    ((o.operation g R).moduleAdjunction.comp (o.operation f R).moduleAdjunction)
    (o.operation (f ≫ g) R).moduleAdjunction).symm (p.comp f g R)).symm

/-- Exact termwise localization of the normalized pullback compositor.
Source: Stacks 015F (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def Spatial.pullComp {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (p : Spatial o) {U V W : Over T}
    (f : U ⟶ V) (g : V ⟶ W) (R : Rings m T) :
    (o.operation g R).left ⋙ (o.operation f R).left ≅
      (o.operation (f ≫ g) R).left :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (p.ordinaryComp f g R)

/-- The identity inverse image is fixed by the same sectionwise identity map.
Source: Stacks 07A6 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def Spatial.pullId {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (p : Spatial o) (W : Over T) (R : Rings m T) :
    (o.operation (𝟙 W) R).left ≅ 𝟭 (category c W R) :=
  Functor.mapDerivedCategoryNatIso
    ((conjugateIsoEquiv (o.operation (𝟙 W) R).moduleAdjunction
      (Adjunction.id : 𝟭 _ ⊣ 𝟭 _)).symm (p.identity W R)).symm ≪≫
        Functor.mapDerivedCategoryIdIso _

/-- Proper derived composition is the unique conjugate of that pullback compositor.
Source: Stacks 0D6E (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def Spatial.pushComp {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (p : Spatial o) {U V W : Over T}
    (f : U ⟶ V) (g : V ⟶ W) (R : Rings m T) :
    (o.operation f R).right ⋙ (o.operation g R).right ≅
      (o.operation (f ≫ g) R).right :=
  (conjugateIsoEquiv
    ((o.operation g R).derivedAdjunction.comp (o.operation f R).derivedAdjunction)
    (o.operation (f ≫ g) R).derivedAdjunction) (p.pullComp f g R).symm

/-- Open extension composition is fixed by the identical composite restriction.
Source: Stacks 03DI (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def Spatial.openComp {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (p : Spatial o) {U V W : Over T}
    (f : U ⟶ V) (g : V ⟶ W)
    [IsOpenImmersion f.left] [IsOpenImmersion g.left] [IsOpenImmersion (f ≫ g).left]
    (R : Rings m T) : o.shriek f R ⋙ o.shriek g R ≅ o.shriek (f ≫ g) R :=
  (((o.openAdjunction f R).comp (o.openAdjunction g R)).ofNatIsoRight
    (p.pullComp f g R)).leftAdjointUniq (o.openAdjunction (f ≫ g) R)

/-- Scalar and geometric comparison presentations, fixed before taking any mates.
Ordinary scalar insertion is exactly `1 tensor x`; the restriction square is identity
on sections. Its adjoint is the ordinary inverse-image/scalar comparison, and the
representative equation fixes its derived version on K-flat complexes.
Source: Stacks 06YY, 03D7, 07A6
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
structure ScalarComparisons {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    (o : Calculus c) where
  ordinaryAdjunction : ∀ (W : Over T) {A B : Rings m T} (a : A ⟶ B),
    (o.scalar W a).E ⊣ restrictScalars
      ((sheafCompose (topology m W.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ((c.rings W).map a))
  insertion : ∀ (W : Over T) {A B : Rings m T} (a : A ⟶ B)
    (M : Mod ((c.rings W).obj A)) (Z : (Site m W.left)ᵒᵖ) (x : M.val.obj Z),
    ((ordinaryAdjunction W a).unit.app M).val.app Z x =
      (eqToHom ((o.scalar W a).obj_eq M).symm).val.app Z
        (SheafOfModules.SuccessiveDerivedQuotient.pure ((c.rings W).map a) M Z 1 x)
  ordinary : ∀ {U V : Over T} (f : U ⟶ V) {A B : Rings m T} (a : A ⟶ B),
    (o.scalar V a).E ⋙ (o.operation f B).pullback ≅
      (o.operation f A).pullback ⋙ (o.scalar U a).E
  restriction : ∀ {U V : Over T} (f : U ⟶ V) {A B : Rings m T} (a : A ⟶ B),
    restrictScalars ((sheafCompose (topology m U.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ((c.rings U).map a)) ⋙
      (o.operation f A).pushforward ≅
      (o.operation f B).pushforward ⋙ restrictScalars
        ((sheafCompose (topology m V.left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ((c.rings V).map a))
  restriction_sections : ∀ {U V : Over T} (f : U ⟶ V) {A B : Rings m T} (a : A ⟶ B)
    (N : Mod ((c.rings U).obj B)) (Z : (Site m V.left)ᵒᵖ),
    ∀ x : N.val.obj ((baseChange m f.left).op.obj Z),
      HEq (((restriction f a).hom.app N).val.app Z x) x
  ordinary_mate : ∀ {U V : Over T} (f : U ⟶ V) {A B : Rings m T} (a : A ⟶ B),
    (conjugateIsoEquiv
      ((ordinaryAdjunction V a).comp (o.operation f B).moduleAdjunction)
      ((o.operation f A).moduleAdjunction.comp (ordinaryAdjunction U a)))
      (ordinary f a).symm = (restriction f a).symm
  pull : ∀ {U V : Over T} (f : U ⟶ V) {A B : Rings m T} (a : A ⟶ B),
    (o.scalar V a).T ⋙ (o.operation f B).left ≅
      (o.operation f A).left ⋙ (o.scalar U a).T
  representative : ∀ {U V : Over T} (f : U ⟶ V) {A B : Rings m T} (a : A ⟶ B)
    (P : CochainComplex (Mod ((c.rings V).obj A)) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients
      (J := topology m V.left) (R := (c.rings V).obj A) P →
    (∀ n : ℤ, IsFlatOnSite (J := topology m V.left) (R := (c.rings V).obj A) (P.X n)) →
    (pull f a).hom.app (DerivedCategory.Q.obj P) ≫
        (o.scalar U a).T.map ((o.operation f A).pullback.mapDerivedCategoryFactors.{u + 2, u + 2,
            u + 1, u + 1, u + 2, u + 2}.hom.app P) ≫
        (o.scalar U a).ε.app
          (((o.operation f A).pullback.mapHomologicalComplex (.up ℤ)).obj P) =
      (o.operation f B).left.map ((o.scalar V a).ε.app P) ≫
        (o.operation f B).pullback.mapDerivedCategoryFactors.{u + 2, u + 2,
          u + 1, u + 1, u + 2, u + 2}.hom.app
          (((o.scalar V a).E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (ordinary f a).hom (.up ℤ)).app P)
  delta : ∀ {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
    {A B : Rings m T} (a : A ⟶ B),
    o.shriek j A ⋙ (o.scalar V a).T ≅ (o.scalar U a).T ⋙ o.shriek j B
  delta_inverse : ∀ {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
    {A B : Rings m T} (a : A ⟶ B) (M : category c U A),
    (o.openAdjunction j B).homEquiv _ _ ((delta j a).inv.app M) =
      (o.scalar U a).T.map ((o.openAdjunction j A).unit.app M) ≫
        (pull j a).inv.app ((o.shriek j A).obj M)

/-- The coefficient comparison is the counit transpose of the canonical scalar
inverse-image comparison. It is never assumed invertible.
Source: Stacks 07A7 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def ScalarComparisons.chi {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (e : ScalarComparisons o) {U V : Over T} (f : U ⟶ V)
    {A B : Rings m T} (a : A ⟶ B) :
    (o.operation f A).right ⋙ (o.scalar V a).T ⟶
      (o.scalar U a).T ⋙ (o.operation f B).right :=
  (mateEquiv (o.operation f A).derivedAdjunction (o.operation f B).derivedAdjunction
    (TwoSquare.mk _ _ _ _ (e.pull f a).hom)).natTrans

/-- The fibre product and its distinguished clopen section. Both projection
identities fix the section; the pullback property fixes the fibre product.
Source: Bhatt--Scholze 6.7.6--6.7.7; Stacks 0F7B
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
structure Shape {T : Scheme.{u}} {X Y Z : Over T} (u : Y ⟶ Z)
    (j₁ : X ⟶ Y) (j₂ : X ⟶ Z) where
  V : Over T
  b : V ⟶ Y
  q : V ⟶ X
  s : X ⟶ V
  pullback : IsPullback b q u j₂
  schemePullback : IsPullback b.left q.left u.left j₂.left
  retraction : s ≫ q = 𝟙 X
  openFactor : s ≫ b = j₁
  [b_open : IsOpenImmersion b.left]
  [s_open : IsOpenImmersion s.left]
  clopen : IsClopen (Set.range s.left.base)

attribute [instance] Shape.b_open Shape.s_open

/-- The normalized inverse-image square in the actual derived categories.
Source: Stacks 03D8 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def Spatial.square {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (p : Spatial o) {V X Y Z : Over T}
    {b : V ⟶ Y} {q : V ⟶ X} {u : Y ⟶ Z} {j : X ⟶ Z}
    (h : b ≫ u = q ≫ j) (R : Rings m T) :
    (o.operation u R).left ⋙ (o.operation b R).left ≅
      (o.operation j R).left ⋙ (o.operation q R).left :=
  p.pullComp b u R ≪≫
    eqToIso (congrArg (fun f ↦ (o.operation f R).left) h) ≪≫ (p.pullComp q j R).symm

/-- Open composition, including a specified equality with another open immersion,
is fixed by the identical composite restriction adjunction.
Source: Stacks 03DI (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def Spatial.openFactor {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (p : Spatial o) {U V W : Over T}
    (f : U ⟶ V) (g : V ⟶ W) (k : U ⟶ W)
    [IsOpenImmersion f.left] [IsOpenImmersion g.left] [IsOpenImmersion k.left]
    (h : f ≫ g = k) (R : Rings m T) :
    o.shriek f R ⋙ o.shriek g R ≅ o.shriek k R :=
  (((o.openAdjunction f R).comp (o.openAdjunction g R)).ofNatIsoRight
    (p.pullComp f g R ≪≫ eqToIso (congrArg (fun a ↦ (o.operation a R).left) h))).leftAdjointUniq
      (o.openAdjunction k R)

/-- The section/retraction restriction is the normalized pullback compositor.
Source: Stacks 03D8 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def Spatial.sectionPull {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (p : Spatial o) {X Y Z : Over T} {u : Y ⟶ Z}
    {j₁ : X ⟶ Y} {j₂ : X ⟶ Z} (d : Shape u j₁ j₂) (R : Rings m T) :
    (o.operation d.q R).left ⋙ (o.operation d.s R).left ≅ 𝟭 (category c X R) :=
  p.pullComp d.s d.q R ≪≫
    eqToIso (congrArg (fun f ↦ (o.operation f R).left) d.retraction) ≪≫ p.pullId X R

/-- The base-change comparison has its open-unit transpose, and the clopen
projection is identity on the distinguished open and zero on its complement.
These equations characterize the actual maps on the whole derived categories.
Source: Stacks 0F7B, 09AE, 03DI
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
structure OpenComparisons {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (p : Spatial o) where
  beta : ∀ {V X Y Z : Over T} (b : V ⟶ Y) (q : V ⟶ X) (u : Y ⟶ Z) (j : X ⟶ Z)
    [IsOpenImmersion b.left] [IsOpenImmersion j.left] (_sq : IsPullback b q u j)
    (R : Rings m T),
    o.shriek j R ⋙ (o.operation u R).left ≅ (o.operation q R).left ⋙ o.shriek b R
  beta_inverse : ∀ {V X Y Z : Over T} (b : V ⟶ Y) (q : V ⟶ X)
    (u : Y ⟶ Z) (j : X ⟶ Z) [IsOpenImmersion b.left] [IsOpenImmersion j.left]
    (sq : IsPullback b q u j) (R : Rings m T) (M : category c X R),
    (o.openAdjunction b R).homEquiv _ _ ((beta b q u j sq R).inv.app M) =
      (o.operation q R).left.map ((o.openAdjunction j R).unit.app M) ≫
        (p.square sq.w R).inv.app ((o.shriek j R).obj M)
  pi : ∀ {U V : Over T} (s : U ⟶ V) [IsOpenImmersion s.left]
    (_hs : IsClopen (Set.range s.left.base)) (R : Rings m T),
    𝟭 (category c V R) ⟶ (o.operation s R).left ⋙ o.shriek s R
  pi_image : ∀ {U V : Over T} (s : U ⟶ V) [IsOpenImmersion s.left]
    (hs : IsClopen (Set.range s.left.base)) (R : Rings m T) (N : category c V R),
    (o.operation s R).left.map ((pi s hs R).app N) =
      (o.openAdjunction s R).unit.app ((o.operation s R).left.obj N)
  pi_complement : ∀ {U V W : Over T} (s : U ⟶ V) [IsOpenImmersion s.left]
    (hs : IsClopen (Set.range s.left.base)) (t : W ⟶ V) [IsOpenImmersion t.left]
    (_ht : Set.range t.left.base = (Set.range s.left.base)ᶜ)
    (R : Rings m T) (N : category c V R),
    (o.operation t R).left.map ((pi s hs R).app N) = 0

/-- The three prescribed factors beta, clopen projection and open composition.
There is no freely chosen h map. Source: Bhatt--Scholze 6.7.6--6.7.7
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def OpenComparisons.h {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} {p : Spatial o} (e : OpenComparisons p)
    {X Y Z : Over T} {u : Y ⟶ Z} {j₁ : X ⟶ Y} {j₂ : X ⟶ Z}
    [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    (d : Shape u j₁ j₂) (R : Rings m T) (M : category c X R) :
    (o.operation u R).left.obj ((o.shriek j₂ R).obj M) ⟶ (o.shriek j₁ R).obj M :=
  (e.beta d.b d.q u j₂ d.pullback R).hom.app M ≫
    (o.shriek d.b R).map ((e.pi d.s d.clopen R).app ((o.operation d.q R).left.obj M)) ≫
    (o.shriek d.b R).map ((o.shriek d.s R).map ((p.sectionPull d R).hom.app M)) ≫
    (p.openFactor d.s d.b j₁ d.openFactor R).hom.app M

/-- Every refinement is the adjunct of the specified clopen h; the adjunct equation
precludes arbitrary refinement maps. Source: Bhatt--Scholze 6.7.6--6.7.7
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
structure Refinements {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} {p : Spatial o} (e : OpenComparisons p) where
  map : ∀ {X Y Z : Over T} (u : Y ⟶ Z) (j₁ : X ⟶ Y) (j₂ : X ⟶ Z)
    [IsProper u.left] [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] (_h : j₁ ≫ u = j₂)
    (_d : Shape u j₁ j₂) (R : Rings m T),
    o.shriek j₂ R ⟶ o.shriek j₁ R ⋙ (o.operation u R).right
  adjunct : ∀ {X Y Z : Over T} (u : Y ⟶ Z) (j₁ : X ⟶ Y) (j₂ : X ⟶ Z)
    [IsProper u.left] [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] (h : j₁ ≫ u = j₂)
    (d : Shape u j₁ j₂) (R : Rings m T) (M : category c X R),
    (o.operation u R).derivedAdjunction.homEquiv _ _ (e.h d R M) =
      (map u j₁ j₂ h d R).app M

/-- Balanced coefficient associators and units, pinned on the same universal
cochain counits as scalar extension. This retains the derived normalization without
any equality of site object and morphism universes.
Source: Stacks 06YY, 0D6D (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
structure ScalarComposition {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    (o : Calculus c) where
  ordinary : ∀ (W : Over T) {A B C : Rings m T} (a : A ⟶ B) (b : B ⟶ C),
    (o.scalar W a).E ⋙ (o.scalar W b).E ≅ (o.scalar W (a ≫ b)).E
  pure : ∀ (W : Over T) {A B C : Rings m T} (a : A ⟶ B) (b : B ⟶ C)
    (M : Mod ((c.rings W).obj A)) (Z : (Site m W.left)ᵒᵖ)
    (x : M.val.obj Z) (y : ((c.rings W).obj B).obj.obj Z)
    (z : ((c.rings W).obj C).obj.obj Z),
    HEq (((ordinary W a b).hom.app M).val.app Z
      ((eqToHom ((o.scalar W b).obj_eq ((o.scalar W a).E.obj M)).symm).val.app Z
        (SuccessiveDerivedQuotient.pure ((c.rings W).map b) ((o.scalar W a).E.obj M) Z z
          ((eqToHom ((o.scalar W a).obj_eq M).symm).val.app Z
            (SuccessiveDerivedQuotient.pure ((c.rings W).map a) M Z y x)))))
      ((eqToHom ((o.scalar W (a ≫ b)).obj_eq M).symm).val.app Z
        (SuccessiveDerivedQuotient.pure ((c.rings W).map (a ≫ b)) M Z
          (((c.rings W).map b).hom.app Z y * z) x))
  derived : ∀ (W : Over T) {A B C : Rings m T} (a : A ⟶ B) (b : B ⟶ C),
    (o.scalar W a).T ⋙ (o.scalar W b).T ≅ (o.scalar W (a ≫ b)).T
  representative : ∀ (W : Over T) {A B C : Rings m T} (a : A ⟶ B) (b : B ⟶ C)
    (P : CochainComplex (Mod ((c.rings W).obj A)) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients
      (J := topology m W.left) (R := (c.rings W).obj A) P →
    (derived W a b).hom.app (DerivedCategory.Q.obj P) ≫
        (o.scalar W (a ≫ b)).ε.app P =
      (o.scalar W b).T.map ((o.scalar W a).ε.app P) ≫
        (o.scalar W b).ε.app (((o.scalar W a).E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (ordinary W a b).hom
          (.up ℤ)).app P)
  ordinaryUnit : ∀ (W : Over T) (A : Rings m T), (o.scalar W (𝟙 A)).E ≅ 𝟭 _
  unit_pure : ∀ (W : Over T) (A : Rings m T) (M : Mod ((c.rings W).obj A))
    (Z : (Site m W.left)ᵒᵖ) (x : M.val.obj Z),
    ((ordinaryUnit W A).hom.app M).val.app Z
      ((eqToHom ((o.scalar W (𝟙 A)).obj_eq M).symm).val.app Z
        (SuccessiveDerivedQuotient.pure ((c.rings W).map (𝟙 A)) M Z 1 x)) = x
  unit : ∀ (W : Over T) (A : Rings m T), (o.scalar W (𝟙 A)).T ≅ 𝟭 _
  unit_representative : ∀ (W : Over T) (A : Rings m T)
    (P : CochainComplex (Mod ((c.rings W).obj A)) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients
      (J := topology m W.left) (R := (c.rings W).obj A) P →
    (unit W A).hom.app (DerivedCategory.Q.obj P) = (o.scalar W (𝟙 A)).ε.app P ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (ordinaryUnit W A).hom
        (.up ℤ)).app P)

/-- The displayed left-hand composite, for an arbitrary unbounded input.
Source: Bhatt--Scholze 6.7.6--6.7.7, coefficient supplement
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def left {m : Mode} {T : Scheme.{u}} {c : Coefficients m T} {o : Calculus c}
    (sc : ScalarComparisons o) {p : Spatial o} {e : OpenComparisons p} (r : Refinements e)
    {X Y Z : Over T} (u : Y ⟶ Z) (j₁ : X ⟶ Y) (j₂ : X ⟶ Z)
    [IsProper u.left] [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] (h : j₁ ≫ u = j₂)
    (d : Shape u j₁ j₂) {A B : Rings m T} (a : A ⟶ B) :
    o.shriek j₂ A ⋙ (o.scalar Z a).T ⟶
      (o.scalar X a).T ⋙ o.shriek j₁ B ⋙ (o.operation u B).right :=
  Functor.whiskerRight (r.map u j₁ j₂ h d A) (o.scalar Z a).T ≫
    Functor.whiskerLeft (o.shriek j₁ A) (sc.chi u a) ≫
      Functor.whiskerRight (sc.delta j₁ a).hom (o.operation u B).right

/-- The displayed right-hand composite.
Source: Bhatt--Scholze 6.7.6--6.7.7, coefficient supplement
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def right {m : Mode} {T : Scheme.{u}} {c : Coefficients m T} {o : Calculus c}
    (sc : ScalarComparisons o) {p : Spatial o} {e : OpenComparisons p} (r : Refinements e)
    {X Y Z : Over T} (u : Y ⟶ Z) (j₁ : X ⟶ Y) (j₂ : X ⟶ Z)
    [IsProper u.left] [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] (h : j₁ ≫ u = j₂)
    (d : Shape u j₁ j₂) {A B : Rings m T} (a : A ⟶ B) :
    o.shriek j₂ A ⋙ (o.scalar Z a).T ⟶
      (o.scalar X a).T ⋙ o.shriek j₁ B ⋙ (o.operation u B).right :=
  (sc.delta j₂ a).hom ≫ Functor.whiskerLeft (o.scalar X a).T (r.map u j₁ j₂ h d B)

/-- The successive coefficient mate with the balanced identifications inserted.
Source: Stacks 0E47 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def successive {m : Mode} {T : Scheme.{u}} {c : Coefficients m T} {o : Calculus c}
    (sc : ScalarComparisons o) (ac : ScalarComposition o) {U V : Over T}
    (f : U ⟶ V) {A B C : Rings m T} (a : A ⟶ B) (b : B ⟶ C) (N : category c U A) :
    (o.scalar V (a ≫ b)).T.obj ((o.operation f A).right.obj N) ⟶
      (o.operation f C).right.obj ((o.scalar U (a ≫ b)).T.obj N) :=
  (ac.derived V a b).inv.app ((o.operation f A).right.obj N) ≫
    (o.scalar V b).T.map ((sc.chi f a).app N) ≫
      (sc.chi f b).app ((o.scalar U a).T.obj N) ≫
        (o.operation f C).right.map ((ac.derived U a b).hom.app N)

set_option backward.isDefEq.respectTransparency false in
/-- Each coherence is an equation of its own canonical maps: the square, input
naturality, balanced coefficient pasting, proper-refinement composition and identity.
All are on ordinary derived categories themselves, before any evaluation or limit.
Source: Bhatt--Scholze 6.7.6--6.7.7, coefficient supplement
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
structure Laws {m : Mode} {T : Scheme.{u}} {c : Coefficients m T} {o : Calculus c}
    (sc : ScalarComparisons o) (ac : ScalarComposition o)
    {p : Spatial o} {e : OpenComparisons p} (r : Refinements e) : Prop where
  square : ∀ {X Y Z : Over T} (u : Y ⟶ Z) (j₁ : X ⟶ Y) (j₂ : X ⟶ Z)
    [IsProper u.left] [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] (h : j₁ ≫ u = j₂)
    (d : Shape u j₁ j₂) {A B : Rings m T} (a : A ⟶ B),
    left sc r u j₁ j₂ h d a = right sc r u j₁ j₂ h d a
  natural : ∀ {X Y Z : Over T} (u : Y ⟶ Z) (j₁ : X ⟶ Y) (j₂ : X ⟶ Z)
    [IsProper u.left] [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] (h : j₁ ≫ u = j₂)
    (d : Shape u j₁ j₂) {A B : Rings m T} (a : A ⟶ B)
    {M N : category c X A} (f : M ⟶ N),
    (o.scalar Z a).T.map ((o.shriek j₂ A).map f) ≫
        (left sc r u j₁ j₂ h d a).app N =
      (left sc r u j₁ j₂ h d a).app M ≫
        (o.operation u B).right.map ((o.shriek j₁ B).map ((o.scalar X a).T.map f))
  coefficient : ∀ {U V : Over T} (f : U ⟶ V) {A B C : Rings m T}
    (a : A ⟶ B) (b : B ⟶ C) (N : category c U A),
    (ac.derived V a b).hom.app ((o.operation f A).right.obj N) ≫
        (sc.chi f (a ≫ b)).app N =
      (o.scalar V b).T.map ((sc.chi f a).app N) ≫
        (sc.chi f b).app ((o.scalar U a).T.obj N) ≫
        (o.operation f C).right.map ((ac.derived U a b).hom.app N)
  open_coefficient : ∀ {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
    {A B C : Rings m T} (a : A ⟶ B) (b : B ⟶ C) (M : category c U A),
    (ac.derived V a b).hom.app ((o.shriek j A).obj M) ≫ (sc.delta j (a ≫ b)).hom.app M =
      (o.scalar V b).T.map ((sc.delta j a).hom.app M) ≫
        (sc.delta j b).hom.app ((o.scalar U a).T.obj M) ≫
        (o.shriek j C).map ((ac.derived U a b).hom.app M)
  coefficient_identity : ∀ {U V : Over T} (f : U ⟶ V) (A : Rings m T)
    (N : category c U A),
    (sc.chi f (𝟙 A)).app N ≫
        (o.operation f A).right.map ((ac.unit U A).hom.app N) =
      (ac.unit V A).hom.app ((o.operation f A).right.obj N)
  coefficient_square : ∀ {U V : Over T} (f : U ⟶ V) {A B C D : Rings m T}
    (a : A ⟶ B) (b : B ⟶ D) (a' : A ⟶ C) (b' : C ⟶ D)
    (h : a ≫ b = a' ≫ b') (N : category c U A),
    successive sc ac f a b N ≫ (o.operation f D).right.map
        (eqToHom (congrArg (fun q ↦ (o.scalar U q).T.obj N) h)) =
      eqToHom (congrArg (fun q ↦ (o.scalar V q).T.obj ((o.operation f A).right.obj N)) h) ≫
        successive sc ac f a' b' N
  open_identity : ∀ {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
    (A : Rings m T) (M : category c U A),
    (sc.delta j (𝟙 A)).hom.app M ≫ (o.shriek j A).map ((ac.unit U A).hom.app M) =
      (ac.unit V A).hom.app ((o.shriek j A).obj M)
  refinements : ∀ {X Y Z W : Over T} (u : Y ⟶ Z) (v : Z ⟶ W)
    (j₁ : X ⟶ Y) (j₂ : X ⟶ Z) (j₃ : X ⟶ W)
    [IsProper u.left] [IsProper v.left] [IsProper (u ≫ v).left]
    [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left] [IsOpenImmersion j₃.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] [QuasiCompact j₃.left]
    (h₁ : j₁ ≫ u = j₂) (h₂ : j₂ ≫ v = j₃) (h₃ : j₁ ≫ (u ≫ v) = j₃)
    (d₁ : Shape u j₁ j₂) (d₂ : Shape v j₂ j₃) (d₃ : Shape (u ≫ v) j₁ j₃)
    (R : Rings m T) (M : category c X R),
    (r.map (u ≫ v) j₁ j₃ h₃ d₃ R).app M =
      (r.map v j₂ j₃ h₂ d₂ R).app M ≫
        (o.operation v R).right.map ((r.map u j₁ j₂ h₁ d₁ R).app M) ≫
        (p.pushComp u v R).hom.app ((o.shriek j₁ R).obj M)
  refinement_identity : ∀ {X Y : Over T} (j : X ⟶ Y)
    [IsOpenImmersion j.left] [QuasiCompact j.left]
    (h : j ≫ 𝟙 Y = j) (d : Shape (𝟙 Y) j j) (R : Rings m T)
    (M : category c X R),
    (r.map (𝟙 Y) j j h d R).app M =
      (o.operation (𝟙 Y) R).derivedAdjunction.homEquiv _ _
        ((p.pullId Y R).hom.app ((o.shriek j R).obj M))
  spatial_coefficient : ∀ {U V W : Over T} (f : U ⟶ V) (g : V ⟶ W)
    {A B : Rings m T} (a : A ⟶ B) (N : category c U A),
    (o.scalar W a).T.map ((p.pushComp f g A).hom.app N) ≫
        (sc.chi (f ≫ g) a).app N =
      (sc.chi g a).app ((o.operation f A).right.obj N) ≫
        (o.operation g B).right.map ((sc.chi f a).app N) ≫
        (p.pushComp f g B).hom.app ((o.scalar U a).T.obj N)

/-- Canonical scalar shifts are fixed by the universal cochain counits.
Refinement and coefficient transformations commute with these actual shifts,
rather than repeating the coefficient-square equation.
Source: Stacks 06YY, 07A6; signed cochain shift calculation
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
structure Shifts {m : Mode} {T : Scheme.{u}} {c : Coefficients m T} {o : Calculus c}
    (sc : ScalarComparisons o) {p : Spatial o} {e : OpenComparisons p}
    (r : Refinements e) where
  [scalar : ∀ (W : Over T) {A B : Rings m T} (a : A ⟶ B), (o.scalar W a).T.CommShift ℤ]
  scalar_counit : ∀ (W : Over T) {A B : Rings m T} (a : A ⟶ B),
    NatTrans.CommShift (o.scalar W a).ε ℤ
  inverse_scalar : ∀ {U V : Over T} (f : U ⟶ V) {A B : Rings m T} (a : A ⟶ B),
    NatTrans.CommShift (sc.pull f a).hom ℤ
  delta : ∀ {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
    {A B : Rings m T} (a : A ⟶ B), NatTrans.CommShift (sc.delta j a).hom ℤ
  chi : ∀ {U V : Over T} (f : U ⟶ V) {A B : Rings m T} (a : A ⟶ B),
    NatTrans.CommShift (sc.chi f a) ℤ
  beta : ∀ {V X Y Z : Over T} (b : V ⟶ Y) (q : V ⟶ X)
    (u : Y ⟶ Z) (j : X ⟶ Z) [IsOpenImmersion b.left] [IsOpenImmersion j.left]
    (sq : IsPullback b q u j) (R : Rings m T),
    NatTrans.CommShift (e.beta b q u j sq R).hom ℤ
  pi : ∀ {U V : Over T} (s : U ⟶ V) [IsOpenImmersion s.left]
    (hs : IsClopen (Set.range s.left.base)) (R : Rings m T),
    NatTrans.CommShift (e.pi s hs R) ℤ
  refinement : ∀ {X Y Z : Over T} (u : Y ⟶ Z) (j₁ : X ⟶ Y) (j₂ : X ⟶ Z)
    [IsProper u.left] [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] (h : j₁ ≫ u = j₂)
    (d : Shape u j₁ j₂) (R : Rings m T), NatTrans.CommShift (r.map u j₁ j₂ h d R) ℤ
  square_left : ∀ {X Y Z : Over T} (u : Y ⟶ Z) (j₁ : X ⟶ Y) (j₂ : X ⟶ Z)
    [IsProper u.left] [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] (h : j₁ ≫ u = j₂)
    (d : Shape u j₁ j₂) {A B : Rings m T} (a : A ⟶ B),
    NatTrans.CommShift (left sc r u j₁ j₂ h d a) ℤ
  square_right : ∀ {X Y Z : Over T} (u : Y ⟶ Z) (j₁ : X ⟶ Y) (j₂ : X ⟶ Z)
    [IsProper u.left] [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] (h : j₁ ≫ u = j₂)
    (d : Shape u j₁ j₂) {A B : Rings m T} (a : A ⟶ B),
    NatTrans.CommShift (right sc r u j₁ j₂ h d a) ℤ

/-- The complete system-independent presentation. Existence is asserted below for
each geometric input, so these are not unproved extra hypotheses on that input.
Source: Bhatt--Scholze 6.7.6--6.7.7, coefficient supplement
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
structure Package (m : Mode) (T : Scheme.{u}) where
  coefficients : Coefficients m T
  operations : Calculus coefficients
  spatial : Spatial operations
  scalars : ScalarComparisons operations
  associators : ScalarComposition operations
  opens : OpenComparisons spatial
  refinements : Refinements opens
  laws : Laws scalars associators refinements
  shifts : Shifts scalars refinements
  shapes : ∀ {X Y Z : Over T} (u : Y ⟶ Z) (j₁ : X ⟶ Y) (j₂ : X ⟶ Z)
    [IsProper u.left] [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] (_h : j₁ ≫ u = j₂),
    Shape u j₁ j₂

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

/-- The underlying additive presheaf functor, with no new module category.
Source: Stacks 03D1 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def additivePresheaf {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u + 1}) :=
  SheafOfModules.forget.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⋙
    PresheafOfModules.toPresheaf.{u + 1} _

/-- Strict tower additive sections, retaining both horizontal and vertical maps.
Source: Stacks 0941, 03D1 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def towerPresheaf (B : Type (u + 1)) [CommRing B] (W : Scheme.{u}) :
    ProEtale.StrictTower.Towers.{u} B W ⥤ ((ℕ × W.ProEt)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (additivePresheaf (ProEtale.StrictTower.coefficients.{u} B W)) ⋙
    Functor.uncurry ⋙ (Functor.whiskeringLeft _ _ _).obj
      (prodOpEquiv (C := ℕ) (D := W.ProEt)).functor

/-- The vertical constant-ring object, so the finite specialization is a strict
constant coefficient system. Source: Stacks 00Z4, 0H7J
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def finiteRing (B : Type (u + 1)) [CommRing B] (T : Scheme.{u}) : Rings .systems T :=
  (constantSheaf (topology .systems T) CommRingCat.{u + 1}).obj (CommRingCat.of.{u + 1} B)

/-- The ordinary constant-section map, before taking its inverse-image adjoint.
Source: Stacks 0H7J (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def finiteDirect (B : Type (u + 1)) [CommRing B] {U T : Scheme.{u}} (f : U ⟶ T) :
    finiteRing B T ⟶ ((baseChange .systems f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology .systems T) (topology .systems U)).obj (finiteRing B U) :=
  ((sheafificationAdjunction (topology .systems T) CommRingCat.{u + 1}).homEquiv _ _).symm
    (Functor.whiskerLeft (baseChange .systems f).op
      (toSheafify (topology .systems U)
        ((Functor.const (Site .systems U)ᵒᵖ).obj (CommRingCat.of.{u + 1} B))))

/-- The specified constant-ring inverse-image map, with no arbitrary scalar action.
Source: Stacks 0H7J (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def finiteInverse (B : Type (u + 1)) [CommRing B] {U T : Scheme.{u}} (f : U ⟶ T) :
    (ringInverse .systems f).obj (finiteRing B T) ⟶ finiteRing B U :=
  ((ringAdjunction .systems f).homEquiv _ _).symm (finiteDirect B f)

/-- A constant scalar section on a single pro-etale site.
Source: Stacks 0H7J (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def finiteScalar (B : Type (u + 1)) [CommRing B] (W : Scheme.{u})
    (Z : W.ProEt) (a : B) :
    CommRingCat.carrier.{u + 1}
      ((ProEtale.StrictTower.coefficients.{u} B W).obj.obj (op Z)) :=
  letI := WeilConjectures.integralCoefficientRingSheafify.{u, 0} W
  (toSheafify.{u, u + 1, u + 1, u + 2} (D := CommRingCat.{u + 1}) (ProEt.topology W)
    ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of.{u + 1} B))).app (op Z) a

/-- A constant scalar section on the vertical system site.
Source: Stacks 0H7J, 00Z4 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def finiteSystemScalar (B : Type (u + 1)) [CommRing B] (W : Scheme.{u})
    (n : ℕ) (Z : W.ProEt) (a : B) : (finiteRing B W).obj.obj (op (n, Z)) :=
  (toSheafify (topology .systems W)
    ((Functor.const (Site .systems W)ᵒᵖ).obj (CommRingCat.of.{u + 1} B))).app (op (n, Z)) a

/-- Finite realization is section-preserving and linear for the canonical constant
scalars. The additive presheaf isomorphism fixes every transition and every map.
This is the diagram-site realization, not an arbitrary equivalence of categories.
Source: Stacks 00Z4, 03D1, 0H7J
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
structure FiniteRealization {T : Scheme.{u}} (P : Package .systems T)
    (B : Type (u + 1)) [CommRing B] (W : Over T) where
  equivalence : ProEtale.StrictTower.Towers.{u} B W.left ≌
    Mod ((P.coefficients.rings W).obj (finiteRing B T))
  [additive : equivalence.functor.Additive]
  underlying : equivalence.functor ⋙
      additivePresheaf ((P.coefficients.rings W).obj (finiteRing B T)) ≅ towerPresheaf B W.left
  constant : (P.coefficients.rings W).obj (finiteRing B T) ≅ finiteRing B W.left
  constant_hom : constant.hom = finiteInverse B W.hom
  scalar : ∀ (N : ProEtale.StrictTower.Towers.{u} B W.left) (n : ℕ) (Z : W.left.ProEt)
    (a : B) (x : (equivalence.functor.obj N).val.obj (op (n, Z))),
    (underlying.hom.app N).app (op (n, Z))
        (constant.inv.hom.app (op (n, Z)) (finiteSystemScalar B W.left n Z a) • x) =
      @SMul.smul ((ProEtale.StrictTower.coefficients.{u} B W.left).obj.obj (op Z))
        ((N.obj (op n)).val.obj (op Z)) inferInstance (finiteScalar B W.left Z a)
        ((underlying.hom.app N).app (op (n, Z)) x)

attribute [instance] FiniteRealization.additive

/-- Exact localization of the prescribed ordinary finite realization.
Source: Stacks 015F (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def FiniteRealization.derived {T : Scheme.{u}} {P : Package .systems T}
    {B : Type (u + 1)} [CommRing B] {W : Over T} (e : FiniteRealization P B W) :=
  letI := WeilConjectures.scalarReductionSiteSmall.{u, 0} W.left
  e.equivalence.functor.mapDerivedCategory.{u + 2, u + 2}

/-- The actual termwise module adjunction used by the strict-tower dependency.
Source: Stacks 07A6 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def finiteOrdinaryAdjunction (B : Type (u + 1)) [CommRing B] {U V : Scheme.{u}}
    (f : U ⟶ V) : ProEtale.StrictTower.towerPullback.{u} B f ⊣
      ProEtale.StrictTower.towerDirectImage.{u} B f :=
  (proEtaleRingModuleAdjunction f (ProEtale.StrictTower.coefficients.{u} B V)
    (ProEtale.StrictTower.coefficients.{u} B U)
    (ProEtale.StrictTower.constantRingIso.{u} B f)).whiskerRight ℕᵒᵖ

/-- The finite inverse-image comparison on its actual cochain representatives.
The fixed smallness proofs select the dependency's original universe; the body is
exactly the localization comparison equation, with no extra premise.
Source: Stacks 015V, 07A6 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def finitePullModel {T : Scheme.{u}} (P : Package .systems T)
    (B : Type (u + 1)) [CommRing B] (e : ∀ W : Over T, FiniteRealization P B W)
    {U V : Over T} (f : U ⟶ V)
    (ordinary : ProEtale.StrictTower.towerPullback.{u} B f.left ⋙ (e U).equivalence.functor ≅
      (e V).equivalence.functor ⋙ (P.operations.operation f (finiteRing B T)).pullback)
    (derived : ProEtale.StrictTower.G.{u} B f.left ⋙ (e U).derived ≅
      (e V).derived ⋙ (P.operations.operation f (finiteRing B T)).left) : Prop :=
  letI := WeilConjectures.scalarReductionSiteSmall.{u, 0} U.left
  letI := WeilConjectures.scalarReductionSiteSmall.{u, 0} V.left
  ∀ (Q : CochainComplex (ProEtale.StrictTower.Towers.{u} B V.left) ℤ),
    derived.hom.app (DerivedCategory.Q.obj Q) ≫
        (P.operations.operation f (finiteRing B T)).left.map
          ((e V).equivalence.functor.mapDerivedCategoryFactors.{u + 2, u + 2}.hom.app Q) ≫
        (P.operations.operation f (finiteRing B T)).pullback.mapDerivedCategoryFactors.{u + 2,
            u + 2, u + 1, u + 1, u + 2, u + 2}.hom.app
          (((e V).equivalence.functor.mapHomologicalComplex (.up ℤ)).obj Q) =
      (e U).derived.map
        ((ProEtale.StrictTower.towerPullback.{u} B f.left).mapDerivedCategoryFactors.{u + 2,
            u + 2}.hom.app Q) ≫
        (e U).equivalence.functor.mapDerivedCategoryFactors.{u + 2, u + 2}.hom.app
          (((ProEtale.StrictTower.towerPullback.{u} B f.left).mapHomologicalComplex
            (.up ℤ)).obj Q) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app Q)

/-- The finite operation comparisons are fixed by ordinary section maps and their
adjunctions, not by an equation asserting the desired refinement conclusion.
Source: Stacks 03D7, 03DI, 07A6
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
structure FiniteComparison {T : Scheme.{u}} (P : Package .systems T)
    (B : Type (u + 1)) [CommRing B] (e : ∀ W : Over T, FiniteRealization P B W) where
  ordinaryPush : ∀ {U V : Over T} (f : U ⟶ V),
    ProEtale.StrictTower.towerDirectImage.{u} B f.left ⋙ (e V).equivalence.functor ≅
      (e U).equivalence.functor ⋙ (P.operations.operation f (finiteRing B T)).pushforward
  push_sections : ∀ {U V : Over T} (f : U ⟶ V)
    (N : ProEtale.StrictTower.Towers.{u} B U.left) (n : ℕ) (Z : V.left.ProEt)
    (x : ((e V).equivalence.functor.obj
      ((ProEtale.StrictTower.towerDirectImage.{u} B f.left).obj N)).val.obj (op (n, Z))),
    HEq ((e U).underlying.hom.app N |>.app (op (n, (baseChange .ordinary f.left).obj Z))
        (((ordinaryPush f).hom.app N).val.app (op (n, Z)) x))
      (((e V).underlying.hom.app
        ((ProEtale.StrictTower.towerDirectImage.{u} B f.left).obj N)).app (op (n, Z)) x)
  ordinaryPull : ∀ {U V : Over T} (f : U ⟶ V),
    ProEtale.StrictTower.towerPullback.{u} B f.left ⋙ (e U).equivalence.functor ≅
      (e V).equivalence.functor ⋙ (P.operations.operation f (finiteRing B T)).pullback
  ordinary_unit : ∀ {U V : Over T} (f : U ⟶ V)
    (M : ProEtale.StrictTower.Towers.{u} B V.left),
    (e V).equivalence.functor.map ((finiteOrdinaryAdjunction B f.left).unit.app M) ≫
        (ordinaryPush f).hom.app ((ProEtale.StrictTower.towerPullback.{u} B f.left).obj M) ≫
        (P.operations.operation f (finiteRing B T)).pushforward.map
          ((ordinaryPull f).hom.app M) =
      (P.operations.operation f (finiteRing B T)).moduleAdjunction.unit.app
        ((e V).equivalence.functor.obj M)
  pull : ∀ {U V : Over T} (f : U ⟶ V),
    ProEtale.StrictTower.G.{u} B f.left ⋙ (e U).derived ≅
      (e V).derived ⋙ (P.operations.operation f (finiteRing B T)).left
  pull_model : ∀ {U V : Over T} (f : U ⟶ V),
    finitePullModel P B e f (ordinaryPull f) (pull f)
  push : ∀ {U V : Over T} (f : U ⟶ V),
    ProEtale.StrictTower.R.{u} B f.left ⋙ (e V).derived ≅
      (e U).derived ⋙ (P.operations.operation f (finiteRing B T)).right
  adjunction : ∀ {U V : Over T} (f : U ⟶ V),
    WeilConjectures.SemilinearSections.AdjunctionEvaluation (e V).derived (e U).derived
      (ProEtale.StrictTower.adj.{u} B f.left)
      (P.operations.operation f (finiteRing B T)).derivedAdjunction
  adjunction_pull : ∀ {U V : Over T} (f : U ⟶ V), (adjunction f).left = pull f
  adjunction_push : ∀ {U V : Over T} (f : U ⟶ V), (adjunction f).right = push f
  shriekIso : ∀ {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left],
    ProEtale.StrictTower.J.{u} B j.left ⋙ (e V).derived ≅
      (e U).derived ⋙ P.operations.shriek j (finiteRing B T)
  open_unit : ∀ {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
    (M : ProEtale.StrictTower.Derived.{u} B U.left),
    (e U).derived.map ((ProEtale.StrictTower.jAdj.{u} B j.left).unit.app M) ≫
        (pull j).hom.app ((ProEtale.StrictTower.J.{u} B j.left).obj M) ≫
        (P.operations.operation j (finiteRing B T)).left.map ((shriekIso j).hom.app M) =
      (P.operations.openAdjunction j (finiteRing B T)).unit.app ((e U).derived.obj M)

/-- The finite comparison identifies the actual normalized strict-tower refinement
mate, including the identity proper map on X; it is not another copy of the square.
Source: Bhatt--Scholze 6.7.6--6.7.7 and the proper/open strict-tower calculus
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def FiniteNormalization {T : Scheme.{u}} (P : Package .systems T)
    (B : Type (u + 1)) [CommRing B] [Finite B]
    (e : ∀ W : Over T, FiniteRealization P B W) (k : FiniteComparison P B e) : Prop :=
  ∀ {X Y Z : Over T} (u : Y ⟶ Z) (j₁ : X ⟶ Y) (j₂ : X ⟶ Z)
    [IsProper u.left] [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] (h : j₁ ≫ u = j₂)
    (d : Shape u j₁ j₂) (M : ProEtale.StrictTower.Derived.{u} B X.left),
    (e Z).derived.map
        ((ProEtale.StrictTower.J.{u} B j₂.left).map
          ((ProEtale.StrictTower.rId.{u} B X.left).inv.app M) ≫
          (ProEtale.StrictTower.gamma.{u} B j₁.left (𝟙 X.left) u.left j₂.left
            ((congrArg (fun f ↦ f.left) h).trans (Category.id_comp j₂.left).symm)).app M) ≫
        (k.push u).hom.app ((ProEtale.StrictTower.J.{u} B j₁.left).obj M) ≫
        (P.operations.operation u (finiteRing B T)).right.map ((k.shriekIso j₁).hom.app M) =
      (k.shriekIso j₂).hom.app M ≫
        (P.refinements.map u j₁ j₂ h d (finiteRing B T)).app ((e X).derived.obj M)

end SheafOfModules.RingedRefinement

