/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.SmoothDatum.TransportGeometricOperations
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportCompact
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarCompatibility
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportGeometry
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleTraceFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCanonicalEtale
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerMap
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCohomologyHom
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.PurityConventions.PurityConventions
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameClass
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorCohomology
public import WeilConjectures.CategoryTheory.Sites.WithSection.TorsorWithSection
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.RingTheory.SmoothFibreRegularLocal
public import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
public import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
public import WeilConjectures.RingTheory.ProperBaseChange.SmoothOverFieldRegularLocal
public import Mathlib.RingTheory.Smooth.Flat
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Regular
public import WeilConjectures.AlgebraicGeometry.EffectiveCartierSum
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceCoordinateBoundaries
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionPurityCoordinates

/-! # Normalizations of smooth trace definitions

Source: current blueprint sec-smooth-purity/sk-def-sp-trace/sk-def-sp-trace-properties.md
(blueprint: new-det-sp-trace-basic-definitions).
The comparisons below use the literal native condensed coefficient functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

private theorem adjunction_comparison_naturality
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G H : D ⥤ C} (a : G ⊣ F) [IsIso a.unit]
    (b : F ⊣ H) {K L : D} (v : K ⟶ L) :
    G.map v ≫ (b.unit.app (G.obj L) ≫ H.map (inv (a.unit.app L))) =
      (b.unit.app (G.obj K) ≫ H.map (inv (a.unit.app K))) ≫ H.map v := by
  have hb := b.unit.naturality (G.map v)
  have ha := (inv a.unit).naturality v
  dsimp only [Functor.id_map, Functor.comp_map] at hb ha
  simp only [NatIso.isIso_inv_app] at ha
  rw [← Category.assoc, hb, Category.assoc, ← H.map_comp, ha, H.map_comp,
    Category.assoc]

/-- Naturality of the canonical open-extension comparison.
Source: naturality of the two adjunction units
(blueprint: new-det-sp-trace-basic-definitions). -/
theorem traceOpenToStar_naturality (c : Coefficient ell) {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] {K L : c.derived ell X} (v : K ⟶ L) :
    (actualOpen (c.obj ell) j).map v ≫ traceOpenToStar ell c j L =
      traceOpenToStar ell c j K ≫ (actualPush (c.obj ell) j).map v :=
  adjunction_comparison_naturality
    (CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction'
      (c.obj ell) j)
    (CondensedRing.derivedUpperStarLowerStarAdjunction (c.obj ell) j) v

/-- The canonical open-to-direct-image comparison as a natural transformation.
Its components are exactly traceOpenToStar.
Source: the two adjunction units
(blueprint: new-det-sp-trace-basic-definitions). -/
def traceOpenToStarNat (c : Coefficient ell) {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] :
    actualOpen (c.obj ell) j ⟶ actualPush (c.obj ell) j where
  app K := traceOpenToStar ell c j K
  naturality _ _ v := traceOpenToStar_naturality ell c j v

/-- The existing direct-image compositor with its two functors explicit.
This is literally lowerComp, with no change of orientation or normalization.
Source: direct-image composition
(blueprint: new-det-sp-trace-basic-definitions). -/
def traceLowerComp (c : Coefficient ell) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    actualPush (c.obj.{u} ell) (f ≫ g) ≅
      actualPush (c.obj.{u} ell) f ⋙ actualPush (c.obj.{u} ell) g :=
  lowerComp (c.obj.{u} ell) f g

/-- The compact-support comparison, formed in the functor category.
Source: the proper coincidence in clause (3)
(blueprint: new-det-sp-trace-basic-definitions). -/
def traceShriekToStarNat (c : Coefficient ell) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (cf : Compactification f) :
    CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cf ⟶
      actualPush (c.obj ell) f :=
  Functor.whiskerRight (traceOpenToStarNat ell c cf.i) (actualPush (c.obj ell) cf.g) ≫
    (traceLowerComp ell c cf.i cf.g).inv ≫
    (eqToIso (congrArg (actualPush (c.obj ell)) cf.comm.symm)).hom

end AlgebraicGeometry.ProEtale.PurityTransport
