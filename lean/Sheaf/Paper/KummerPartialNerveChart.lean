/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.KummerSuccessiveDescent
public import Sheaf.Paper.TameRootTowerExtension
public import Sheaf.Paper.PartialKummerBoundaryUnitModel
public import Sheaf.CategoryTheory.CondensedProductBarComparison
public import Sheaf.Paper.KummerParameterizedTerm
public import Sheaf.Paper.KummerNerveCoordinates
public import Sheaf.Paper.KummerChartGeometryMaps
public import Sheaf.Paper.KummerNormalizedChart
public import Sheaf.Paper.KummerRefinement
public import Sheaf.Paper.KummerCoefficientModels

/-! # Normalized successive Kummer root-chart data

Source: blueprint main-20261015, direct-image stability proof paragraph (3),
agent-expanded successive root nerves. Exact all-continuous geometric reference WANTED.
(blueprint: def-sfb-kummer-partial-nerve-chart).

## Main definitions

* `LisseRootExtension`: actual equivariant extension and its puncture identification.
* `FieldChart`: compatible finite coefficients and coherent normalized descent.
* `NormalizedRefinement`: exact pullback law for the geometric comparison.
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

/-- The existing all-continuous ring, bundled with its actual commutative multiplication.
Source: direct-image proof (3), C_F
(blueprint: def-sfb-kummer-partial-nerve-chart). -/
abbrev fieldRing (F : Type) [NormedField F] : CategoryTheory.CondensedBar.Ring.{u} :=
  CondensedRing.kummerCoefficientRing F

/-- The canonical puncture identification, factored through the actual extension.
Source: direct-image proof (3), restriction and point-pullback coherence
(blueprint: def-sfb-kummer-partial-nerve-chart). -/
def extensionPunctureIso (R : CategoryTheory.CondensedBar.Ring.{u})
    {V T W U : Scheme.{u}} (j : V ⟶ T) (v : V ⟶ W) (a : W ⟶ U)
    (d : V ⟶ U) (h : v ≫ a = d)
    (L : PartialKummer.SchemeModules R.X U)
    (N : PartialKummer.SchemeModules R.X T) (M : Modules R.toMon)
    (r : (CondensedRing.upperStar R.X j).obj N ≅ (CondensedRing.upperStar R.X d).obj L)
    (c : N ≅ ((upperStarFromPoint T).mapMod R.X).obj M) :
    (CondensedRing.upperStar R.X v).obj ((CondensedRing.upperStar R.X a).obj L) ≅
      ((upperStarFromPoint V).mapMod R.X).obj M :=
  ((CondensedRing.upperStarComp R.X v a).app L).symm ≪≫
    (CondensedRing.upperStarCongr R.X h).app L ≪≫ r.symm ≪≫
    (CondensedRing.upperStar R.X j).mapIso c ≪≫
    (CondensedRing.fromCondensedPullbackIso R.X j).app M



section Refinements
variable (R : CategoryTheory.CondensedBar.Ring.{u}) (G : Profinite.{u})
  [CommGroup G] [IsTopologicalGroup G]
  [CategoryTheory.CondensedBar.ActionAbelian R G]
  [IsGrothendieckAbelian.{u + 1} (ActionModule R.toMon G)]
  [HasDerivedCategory.{u + 2} (ActionModule R.toMon G)]
  [HasDerivedCategory.{u + 2} (Modules R.toMon)]

/-- The exact Cartesian restriction law for a normalized local root chart.
The restricted comparison still has an actual augmented coherent nerve model.
Source: direct-image proof (3), common refinements
(blueprint: def-sfb-kummer-partial-nerve-chart). -/
def NormalizedRefinement (B : CategoryTheory.CondensedBar.Model R G)
    {V T W U S : Scheme.{u}} (action : ProfiniteCoefficientAction V G)
    (v : V ⟶ W) (hv : action.act ≫ v = coefficientParameterProjection V G ≫ v)
    (j : V ⟶ T) (q : T ⟶ U) (a : W ⟶ U) (hj : j ≫ q = v ≫ a)
    (i : S ⟶ T) (s : S ⟶ U) (hi : i ≫ q = s)
    (L : PartialKummer.SchemeModules R.X W) (M : ActionModule R.toMon G)
    (N : CondensedRing.KummerNormalizedChart R G B action v hv j q a hj i s hi L M) : Prop :=
  ∀ (S' : Scheme.{u}) (f : S' ⟶ S),
    ∃ restricted : CondensedRing.KummerNormalizedChart R G B action v hv j q a hj
      (f ≫ i) (f ≫ s) ((Category.assoc f i q).trans (congrArg (fun t ↦ f ≫ t) hi)) L M,
      restricted.descent.comparison.hom =
        (CondensedRing.kummerDerivedUpperComp R.X f s).hom.app _ ≫
          (CondensedRing.upperStar R.X f).mapDerivedCategory.map N.descent.comparison.hom ≫
          (CondensedRing.kummerInvariantPullbackIso R G B f M).hom
end Refinements

section Chart
variable {p : ℕ} {Y : Scheme.{u}} {A : Type u} [Finite A] [DecidableEq A]
  {C : A → Y.IdealSheafData} {J Jo Ji : Finset A}
  (D : Y.IdealSheafData) (c : TameRootExtensionChart C J)
  (split : DeckSplit p Jo Ji J) (g : TameRootChartGeometry p D c)

/-- The actual lisse root extension over a fixed bundled ring, retaining the
full linearization, puncture restriction and point-pullback normalization.
Source: direct-image proof (3), extension on the full root tower
(blueprint: def-sfb-kummer-partial-nerve-chart). -/
structure LisseRootExtension (R : CategoryTheory.CondensedBar.Ring.{u})
    (D : Y.IdealSheafData) (c : TameRootExtensionChart C J)
    (g : TameRootChartGeometry p D c)
    (L : PartialKummer.SchemeModules R.X (tameBoundaryOpen D).toScheme)
    (M : Modules R.toMon) where
  extension : PartialKummer.SchemeModules R.X (c.tower p)
  lisse : IsLisseCoefficientModule R.X extension
  linearization : ProfiniteCoefficientLinearization R.X g.action extension
  restriction : (CondensedRing.upperStar R.X (c.openInclusion p D)).obj
      extension ≅ (CondensedRing.upperStar R.X (c.toOpen p D)).obj L
  restriction_equivariant : IsTameRootEquivariantIso R.X
    g.openAction.act (coefficientParameterProjection _ _) 
    (coefficientLinearizationRestriction R.X
      g.openAction.act g.action.act (c.openInclusion p D) g.openEquivariant
      (coefficientParameterProjectionCommutes (c.openInclusion p D) _)
      extension linearization.iso)
    (coefficientDeckDescent R.X g.openAction.act (c.toOpen p D)
      g.overOpen L) restriction
  constant : extension ≅
    ((upperStarFromPoint (c.tower p)).mapMod R.X).obj M

/-- The existing all-continuous condensation with the published ring bundle in
its type. No coefficient object or action is changed.
Source: direct-image proof (3), boundary module
(blueprint: def-sfb-kummer-partial-nerve-chart). -/
def condensationForRing {E : Type} [NormedField E]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : PartialKummer.FiniteRepresentation E G) (F : Type) [NormedField F]
    (ι : E →+* F) (d : PartialKummer.Condensation M F ι) :
    ActionModule (fieldRing F).toMon G := d.object

/-- One actual lisse extension, its linearization and its normalized puncture and
point-pullback identifications, before any derived descent data is supplied.
Source: direct-image proof (3), the root-tower extension
(blueprint: def-sfb-kummer-partial-nerve-chart). -/
structure FieldExtension {E : Type} [NormedField E]
    (M : PartialKummer.FiniteRepresentation E
      (ParameterRootDeckGroup p {a : A // a ∈ Jo} ×
        ParameterRootDeckGroup p {a : A // a ∈ Ji}))
    (F : Type) [NormedField F] (ι : E →+* F)
    (L : PartialKummer.SchemeModules (fieldRing F).X (tameBoundaryOpen D).toScheme) where
  condensation : PartialKummer.Condensation M F ι
  root : LisseRootExtension (fieldRing F) D c g L
    (condensationForRing M F ι condensation).module

/-- The already supplied condensation with its bundled coefficient ring fixed.
This is the same action module, not a replacement construction.
Source: direct-image proof (3), the actual boundary coefficient
(blueprint: def-sfb-kummer-partial-nerve-chart). -/
def FieldExtension.coefficientModule {E F : Type} [NormedField E] [NormedField F]
    {ι : E →+* F} {M : PartialKummer.FiniteRepresentation E
      (ParameterRootDeckGroup p {a : A // a ∈ Jo} ×
        ParameterRootDeckGroup p {a : A // a ∈ Ji})}
    {L : PartialKummer.SchemeModules (fieldRing F).X (tameBoundaryOpen D).toScheme}
    (d : FieldExtension D c g M F ι L) :
    ActionModule (fieldRing F).toMon
      (ParameterRootDeckGroup p {a : A // a ∈ Jo} ×
        ParameterRootDeckGroup p {a : A // a ∈ Ji}) := condensationForRing M F ι d.condensation

/-- Resolved successive-nerve data over one fixed ring and coefficient object.
Every comparison retains the actual geometric augmentation and counit squares.
Source: direct-image proof (3), normalized successive descent
(blueprint: def-sfb-kummer-partial-nerve-chart). -/
structure ResolvedFullRootChart (R : CategoryTheory.CondensedBar.Ring.{u})
    (D : Y.IdealSheafData) (c : TameRootExtensionChart C J)
    (split : DeckSplit p Jo Ji J) (g : TameRootChartGeometry p D c)
    [e : Environment R
      (ParameterRootDeckGroup p {a : A // a ∈ Jo})
      (ParameterRootDeckGroup p {a : A // a ∈ Ji})]
    (L : PartialKummer.SchemeModules R.X (tameBoundaryOpen D).toScheme)
    (M : ActionModule R.toMon
      (ParameterRootDeckGroup p {a : A // a ∈ Jo} ×
        ParameterRootDeckGroup p {a : A // a ∈ Ji}))
    (data : LisseRootExtension R D c g L M.module)
    (i : c.boundary ⟶ c.tower p) (hi : i ≫ c.towerMap p = c.boundaryToBase) where
  productAction : ProfiniteCoefficientAction (c.punctured p D)
    (Profinite.of (ParameterRootDeckGroup p {a : A // a ∈ Jo} ×
      ParameterRootDeckGroup p {a : A // a ∈ Ji}))
  productAction_eq : productAction.act = coefficientActionFamily g.openAction.act
    (Profinite.of (ParameterRootDeckGroup p {a : A // a ∈ Jo} ×
      ParameterRootDeckGroup p {a : A // a ∈ Ji}))
      ⟨split.equiv.symm, split.equiv.symm.continuous_toFun⟩
  overQuotient : productAction.act ≫ c.toPuncturedBase p D =
    coefficientParameterProjection _ _ ≫ c.toPuncturedBase p D
  doubleNerve : DoubleNerve
    (Profinite.of (ParameterRootDeckGroup p {a : A // a ∈ Jo}))
    (Profinite.of (ParameterRootDeckGroup p {a : A // a ∈ Ji}))
    productAction (c.toPuncturedBase p D) overQuotient
  normalizedNerve : @CondensedRing.KummerNormalizedChart R
    (Profinite.of (ParameterRootDeckGroup p {a : A // a ∈ Jo} ×
      ParameterRootDeckGroup p {a : A // a ∈ Ji}))
    inferInstance inferInstance e.abelian e.productGroth e.productDerived e.modulesDerived e.full
    (c.punctured p D) (c.tower p) (c.puncturedBase D) c.U c.boundary
    productAction (c.toPuncturedBase p D) overQuotient
    (c.openInclusion p D) (c.towerMap p) (CondensedRing.kummerChartOpen D c)
    (CondensedRing.kummerChartOpen_commutes p D c)
    i c.boundaryToBase hi
    ((CondensedRing.upperStar R.X (CondensedRing.kummerChartToOpen D c)).obj L)
    M
  puncture_normalization : normalizedNerve.punctured =
    extensionPunctureIso R (c.openInclusion p D)
      (c.toPuncturedBase p D) (CondensedRing.kummerChartToOpen D c) (c.toOpen p D)
      (CondensedRing.kummerChartToOpen_commutes p D c) L data.extension
      M.module data.restriction data.constant

  refinement : NormalizedRefinement R
    (Profinite.of (ParameterRootDeckGroup p {a : A // a ∈ Jo} ×
      ParameterRootDeckGroup p {a : A // a ∈ Ji})) e.full
    productAction (c.toPuncturedBase p D) overQuotient
    (c.openInclusion p D) (c.towerMap p) (CondensedRing.kummerChartOpen D c)
    (CondensedRing.kummerChartOpen_commutes p D c) i c.boundaryToBase hi
    ((CondensedRing.upperStar R.X (CondensedRing.kummerChartToOpen D c)).obj L)
    M normalizedNerve


/-- Full and successive geometric descents over the same actual root chart.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-partial-nerve-chart). -/
structure ResolvedRootData (R : CategoryTheory.CondensedBar.Ring.{u})
    (D : Y.IdealSheafData) (c : TameRootExtensionChart C J)
    (split : DeckSplit p Jo Ji J) (g : TameRootChartGeometry p D c)
    [e : Environment R
      (ParameterRootDeckGroup p {a : A // a ∈ Jo})
      (ParameterRootDeckGroup p {a : A // a ∈ Ji})]
    (L : PartialKummer.SchemeModules R.X (tameBoundaryOpen D).toScheme)
    (M : ActionModule R.toMon
      (ParameterRootDeckGroup p {a : A // a ∈ Jo} ×
        ParameterRootDeckGroup p {a : A // a ∈ Ji}))
    (data : LisseRootExtension R D c g L M.module)
    (i : c.boundary ⟶ c.tower p) (hi : i ≫ c.towerMap p = c.boundaryToBase) where
  full : ResolvedFullRootChart R D c split g L M data i hi

  successive : SuccessiveDescent R
    (Profinite.of (ParameterRootDeckGroup p {a : A // a ∈ Jo}))
    (Profinite.of (ParameterRootDeckGroup p {a : A // a ∈ Ji}))
    full.doubleNerve (c.openInclusion p D) (c.towerMap p) (CondensedRing.kummerChartOpen D c)
    (CondensedRing.kummerChartOpen_commutes p D c) i c.boundaryToBase hi
    ((CondensedRing.upperStar R.X (CondensedRing.kummerChartToOpen D c)).obj L) M
    full.normalizedNerve.punctured full.normalizedNerve.descent.resolution
    full.normalizedNerve.descent.actionResolution
    full.normalizedNerve.descent.barResolution.underlying
    full.normalizedNerve.descent.barResolution.underlyingIso
/-- Equality with the full geometric augmentation and exact successive refinement.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-partial-nerve-chart). -/
def ResolvedRootLaws (R : CategoryTheory.CondensedBar.Ring.{u})
    (D : Y.IdealSheafData) (c : TameRootExtensionChart C J)
    (split : DeckSplit p Jo Ji J) (g : TameRootChartGeometry p D c)
    [e : Environment R
      (ParameterRootDeckGroup p {a : A // a ∈ Jo})
      (ParameterRootDeckGroup p {a : A // a ∈ Ji})]
    (L : PartialKummer.SchemeModules R.X (tameBoundaryOpen D).toScheme)
    (M : ActionModule R.toMon
      (ParameterRootDeckGroup p {a : A // a ∈ Jo} ×
        ParameterRootDeckGroup p {a : A // a ∈ Ji}))
    (data : LisseRootExtension R D c g L M.module)
    (i : c.boundary ⟶ c.tower p) (hi : i ≫ c.towerMap p = c.boundaryToBase)
    (d : ResolvedRootData R D c split g L M data i hi) : Prop :=
  (HEq ((CondensedRing.kummerResolutionComparison R.X (CondensedRing.kummerChartOpen D c)
      c.boundaryToBase d.full.normalizedNerve.descent.resolution).hom ≫
      (smallQ R c.boundary).map d.successive.totals.data.diagonalAugmentation ≫
        d.successive.totals.data.diagonalComparison.hom)
    (d.full.normalizedNerve.descent.comparison.hom ≫
      (CondensedRing.kummerPointPullBig R c.boundary).map
        (e.full.invariants.functor.rightDerivedFunctor.map (degreeZeroIso M).inv ≫
          (e.comparison M d.full.normalizedNerve.descent.actionResolution).diagonalIso.hom))) ∧
    d.successive.Refines

/-- Full and successive descents with both their geometric normalization laws.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-partial-nerve-chart). -/
structure ResolvedRootChart (R : CategoryTheory.CondensedBar.Ring.{u})
    (D : Y.IdealSheafData) (c : TameRootExtensionChart C J)
    (split : DeckSplit p Jo Ji J) (g : TameRootChartGeometry p D c)
    [e : Environment R
      (ParameterRootDeckGroup p {a : A // a ∈ Jo})
      (ParameterRootDeckGroup p {a : A // a ∈ Ji})]
    (L : PartialKummer.SchemeModules R.X (tameBoundaryOpen D).toScheme)
    (M : ActionModule R.toMon
      (ParameterRootDeckGroup p {a : A // a ∈ Jo} ×
        ParameterRootDeckGroup p {a : A // a ∈ Ji}))
    (data : LisseRootExtension R D c g L M.module)
    (i : c.boundary ⟶ c.tower p) (hi : i ≫ c.towerMap p = c.boundaryToBase) where
  model : ResolvedRootData R D c split g L M data i hi
  laws : ResolvedRootLaws R D c split g L M data i hi model

/-- Extension and normalized full and successive geometric nerves for one field.
The point-pullback
identification specifies the finite continuous boundary module. The puncture
identification is exactly its composite with the actual extension restriction.
Every column of normalizedNerve is fixed by the full-root unit and counit mate.
Source: direct-image proof (3), simultaneous lisse root extensions and augmentations
(blueprint: def-sfb-kummer-partial-nerve-chart). -/
structure FieldChart {E : Type} [NormedField E]
    (M : PartialKummer.FiniteRepresentation E
      (ParameterRootDeckGroup p {a : A // a ∈ Jo} ×
        ParameterRootDeckGroup p {a : A // a ∈ Ji}))
    (F : Type) [NormedField F] (ι : E →+* F)
    [e : Environment (fieldRing F)
      (ParameterRootDeckGroup p {a : A // a ∈ Jo})
      (ParameterRootDeckGroup p {a : A // a ∈ Ji})]
    (L : PartialKummer.SchemeModules (fieldRing F).X (tameBoundaryOpen D).toScheme)
    (i : c.boundary ⟶ c.tower p) (hi : i ≫ c.towerMap p = c.boundaryToBase) where
  data : FieldExtension D c g M F ι L
  resolved : ResolvedRootChart (fieldRing F) D c split g L data.coefficientModule
    data.root i hi

end Chart

end AlgebraicGeometry.ProEtale.KummerPartialNerve
