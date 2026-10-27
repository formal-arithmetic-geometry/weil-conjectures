/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.KummerPartialNerveChart
public import Sheaf.Paper.TameRootTowerExtension
public import Sheaf.Paper.PartialKummerBoundaryUnitModel
public import Sheaf.CategoryTheory.CondensedProductBarComparison
public import Sheaf.Paper.KummerParameterizedTerm
public import Sheaf.Paper.KummerNerveCoordinates
public import Sheaf.Paper.KummerChartGeometryMaps
public import Sheaf.Paper.KummerNormalizedChart
public import Sheaf.Paper.KummerRefinement
public import Sheaf.Paper.KummerCoefficientModels


/-! # Morphisms of resolved successive Kummer charts

Source: main-20261015 direct-images proof paragraph (3), extracted argument.
Exact all-continuous geometric reference WANTED.
(blueprint: def-sfb-kummer-partial-nerve-morphism).

## Main definitions

* `CoefficientMorphism`: actual puncture, equivariance and derived naturality squares.
* `FieldChart.successiveAugmentation`: the specified augmented derived arrow.
* `UniqueLisseExtensions`: full faithfulness on actual tower refinements.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.KummerPartialNerve
open Profinite.CondensedAction
/-- The map induced by an actual puncture-module morphism on the localized derived image.
Source: direct-image proof (3), arrow naturality
(blueprint: def-sfb-kummer-partial-nerve-morphism). -/
def geometricImageMap (R : CategoryTheory.CondensedBar.Ring.{u})
    {W U S : Scheme.{u}} (a : W ⟶ U) (s : S ⟶ U)
    {L L' : CondensedRing.KummerModules R.X W} (f : L ⟶ L') :
    CondensedRing.kummerOpenImage R.X a s L ⟶ CondensedRing.kummerOpenImage R.X a s L' :=
  (CondensedRing.upperStar R.X s).mapDerivedCategory.map
    ((CondensedRing.moduleObjectDerivedPushforward R.X a).map
      ((DerivedCategory.singleFunctor _ 0).map f))

section Chart
variable {p : ℕ} {Y : Scheme.{u}} {A : Type u} [Finite A] [DecidableEq A]
  {C : A → Y.IdealSheafData} {J Jo Ji : Finset A}
  (D : Y.IdealSheafData) (c : TameRootExtensionChart C J)
  (split : DeckSplit p Jo Ji J) (g : TameRootChartGeometry p D c)

/-- The actual geometric augmentation into the successive total. It starts with
the resolved Cech augmentation of the supplied chart and uses the specified
invariant augmentations, with the canonical degree-zero transport.
Source: direct-image proof (3), the successive augmentation arrow
(blueprint: def-sfb-kummer-partial-nerve-morphism). -/
def FieldChart.successiveAugmentation {E : Type} [NormedField E]
    {M : PartialKummer.FiniteRepresentation E
      (ParameterRootDeckGroup p {a : A // a ∈ Jo} ×
        ParameterRootDeckGroup p {a : A // a ∈ Ji})}
    {F : Type} [NormedField F] {ι : E →+* F}
    [e : Environment (fieldRing F)
      (ParameterRootDeckGroup p {a : A // a ∈ Jo})
      (ParameterRootDeckGroup p {a : A // a ∈ Ji})]
    {L : PartialKummer.SchemeModules (fieldRing F).X (tameBoundaryOpen D).toScheme}
    {i : c.boundary ⟶ c.tower p} {hi : i ≫ c.towerMap p = c.boundaryToBase}
    (P : FieldChart D c split g M F ι L i hi) :=
  P.resolved.model.successive.augmentationArrow

/-- Actual morphism naturality for both geometric nerves: the full-nerve comparison
and the successive geometric augmentation commute with the actual puncture map and
the condensed coefficient arrow under their respective derived invariant functors.
Source: direct-image proof (3), naturality in the puncture morphism
(blueprint: def-sfb-kummer-partial-nerve-morphism). -/
def FieldNatural {E : Type} [NormedField E]
    {M M' : PartialKummer.FiniteRepresentation E
      (ParameterRootDeckGroup p {a : A // a ∈ Jo} ×
        ParameterRootDeckGroup p {a : A // a ∈ Ji})}
    {F : Type} [NormedField F] {ι : E →+* F}
    [e : Environment (fieldRing F)
      (ParameterRootDeckGroup p {a : A // a ∈ Jo})
      (ParameterRootDeckGroup p {a : A // a ∈ Ji})]
    {L L' : PartialKummer.SchemeModules (fieldRing F).X (tameBoundaryOpen D).toScheme}
    {i : c.boundary ⟶ c.tower p} {hi : i ≫ c.towerMap p = c.boundaryToBase}
    (P : FieldChart D c split g M F ι L i hi)
    (Q : FieldChart D c split g M' F ι L' i hi)
    (f : L ⟶ L') (m : P.data.coefficientModule ⟶ Q.data.coefficientModule) : Prop :=
  geometricImageMap (fieldRing F) (CondensedRing.kummerChartOpen D c)
      c.boundaryToBase ((CondensedRing.upperStar (fieldRing F).X
        (CondensedRing.kummerChartToOpen D c)).map f) ≫
      Q.resolved.model.full.normalizedNerve.descent.comparison.hom =
    P.resolved.model.full.normalizedNerve.descent.comparison.hom ≫
      (CondensedRing.kummerPointPullBig (fieldRing F) c.boundary).map
        (e.full.invariants.functor.rightDerivedFunctor.map
          ((DerivedCategory.singleFunctor _ 0).map m)) ∧
  geometricImageMap (fieldRing F) (CondensedRing.kummerChartOpen D c)
      c.boundaryToBase ((CondensedRing.upperStar (fieldRing F).X
        (CondensedRing.kummerChartToOpen D c)).map f) ≫
      FieldChart.successiveAugmentation D c split g Q =
    FieldChart.successiveAugmentation D c split g P ≫
      (CondensedRing.kummerPointPullBig (fieldRing F) c.boundary).map
        ((e.inner.functor.rightDerivedFunctor ⋙ e.outer.functor.rightDerivedFunctor).map
          ((DerivedCategory.singleFunctor _ 0).map m))

end Chart
/-- The ordinary scalar-extension functor over fixed bundled coefficient rings.
Its data is the existing internal module extension of scalars.
Source: direct-image proof (3), ordinary change of continuous coefficient ring
(blueprint: def-sfb-kummer-partial-nerve-morphism). -/
def extendCoefficients (R S : CategoryTheory.CondensedBar.Ring.{u}) (a : R ⟶ S)
    (X : Scheme.{u}) :
    PartialKummer.SchemeModules R.X X ⥤ PartialKummer.SchemeModules S.X X :=
  Mod.extendScalars (coefficientMap a.hom.hom X)

/-- The actual ordinary scalar extension, on objects and arrows alike.
Source: direct-image proof (3), C_Omega tensor over C_E
(blueprint: def-sfb-kummer-partial-nerve-morphism). -/
abbrev extendToClosure (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (X : Scheme.{u}) :=
  extendCoefficients (fieldRing E.1) (fieldRing (PadicAlgCl ℓ))
    (CondensedRing.kummerCoefficientMap ℓ E) X

/-- Canonical scalar extension of a puncture identification, using inverse-image
coherence alone. No direct image occurs in this map.
Source: direct-image proof (3), the actual ordinary Omega extension
(blueprint: def-sfb-kummer-partial-nerve-morphism). -/
def scalarPunctureIso (R S : CategoryTheory.CondensedBar.Ring.{u}) (a : R ⟶ S)
    {V T W : Scheme.{u}} (j : V ⟶ T) (d : V ⟶ W)
    (N : PartialKummer.SchemeModules R.X T) (L : PartialKummer.SchemeModules R.X W)
    (r : (CondensedRing.upperStar R.X j).obj N ≅ (CondensedRing.upperStar R.X d).obj L) :
    (CondensedRing.upperStar S.X j).obj
        ((extendCoefficients R S a T).obj N) ≅
      (CondensedRing.upperStar S.X d).obj
        ((extendCoefficients R S a W).obj L) :=
  ((CondensedRing.pullIso (Λ := R.X) (Λ' := S.X) a.hom.hom j).app N).symm ≪≫
    (extendCoefficients R S a V).mapIso r ≪≫
    (CondensedRing.pullIso (Λ := R.X) (Λ' := S.X) a.hom.hom d).app L

/-- Full faithfulness of puncture restriction for supplied lisse extensions,
including their actual restrictions under every pro-etale base change of the tower.
The isomorphism clause records unique identity-restricting comparisons explicitly.
Source: direct-image proof (3), uniqueness and further common refinements
(blueprint: def-sfb-kummer-partial-nerve-morphism). -/
def UniqueLisseExtensions (R : CategoryTheory.CondensedBar.Ring.{u})
    {X W : Scheme.{u}} (j : W ⟶ X) : Prop :=
  ∀ (Z : Scheme.{u}) (z : Z ⟶ X), WeaklyEtale z →
    ∀ (N N' : PartialKummer.SchemeModules R.X Z),
      IsLisseCoefficientModule R.X N → IsLisseCoefficientModule R.X N' →
      Function.Bijective (fun f : N ⟶ N' ↦
        (CondensedRing.upperStar R.X (pullback.snd j z)).map f) ∧
      ∀ e : (CondensedRing.upperStar R.X (pullback.snd j z)).obj N ≅
        (CondensedRing.upperStar R.X (pullback.snd j z)).obj N',
        ∃! e' : N ≅ N', (CondensedRing.upperStar R.X (pullback.snd j z)).mapIso e' = e

section Morphisms
variable {p : ℕ} {Y : Scheme.{u}} {A : Type u} [Finite A] [DecidableEq A]
  {C : A → Y.IdealSheafData} {J Jo Ji : Finset A}

/-- One field's extension arrow, with its actual puncture, linearization,
point-pullback and derived-geometric naturality equations.
Source: direct-image proof (3), naturality before and after descent
(blueprint: def-sfb-kummer-partial-nerve-morphism). -/
structure CoefficientMorphism (D : Y.IdealSheafData) (c : TameRootExtensionChart C J)
    (split : DeckSplit p Jo Ji J) (g : TameRootChartGeometry p D c)
    {E F : Type} [NormedField E] [NormedField F] {ι : E →+* F}
    [e : Environment (fieldRing F)
      (ParameterRootDeckGroup p {a : A // a ∈ Jo})
      (ParameterRootDeckGroup p {a : A // a ∈ Ji})]
    {M M' : PartialKummer.FiniteRepresentation E
      (ParameterRootDeckGroup p {a : A // a ∈ Jo} ×
        ParameterRootDeckGroup p {a : A // a ∈ Ji})}
    {L L' : PartialKummer.SchemeModules (fieldRing F).X (tameBoundaryOpen D).toScheme}
    {i : c.boundary ⟶ c.tower p} {hi : i ≫ c.towerMap p = c.boundaryToBase}
    (P : FieldChart D c split g M F ι L i hi)
    (Q : FieldChart D c split g M' F ι L' i hi) (f : L ⟶ L') where
  extensionMap : P.data.root.extension ⟶ Q.data.root.extension
  puncture_map :
    (CondensedRing.upperStar (fieldRing F).X (c.openInclusion p D)).map extensionMap ≫
        Q.data.root.restriction.hom = P.data.root.restriction.hom ≫
      (CondensedRing.upperStar (fieldRing F).X (c.toOpen p D)).map f
  equivariant :
    (CondensedRing.upperStar (fieldRing F).X g.action.act).map extensionMap ≫
        Q.data.root.linearization.iso.hom = P.data.root.linearization.iso.hom ≫
      (CondensedRing.upperStar (fieldRing F).X
        (coefficientParameterProjection _ _)).map extensionMap
  boundaryMap : P.data.coefficientModule ⟶ Q.data.coefficientModule
  constant_map : extensionMap ≫ Q.data.root.constant.hom = P.data.root.constant.hom ≫
    ((upperStarFromPoint (c.tower p)).mapMod (fieldRing F).X).map boundaryMap.val
  naturality : FieldNatural D c split g (F := F) (ι := ι) P Q f boundaryMap

end Morphisms

end AlgebraicGeometry.ProEtale.KummerPartialNerve
