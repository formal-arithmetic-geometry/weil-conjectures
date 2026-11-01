/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientProjectionDataSupplement

public import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientPullbackComparisonSupplement
public import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientPullbackShifts
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientScalarUnits
public import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedProjectionRestriction
public import WeilConjectures.AlgebraicGeometry.Picard.SuccessiveDerivedQuotientNormalization
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.Open.OpenSectionClopen

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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

set_option backward.isDefEq.respectTransparency false in
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

end SheafOfModules.RingedRefinement
