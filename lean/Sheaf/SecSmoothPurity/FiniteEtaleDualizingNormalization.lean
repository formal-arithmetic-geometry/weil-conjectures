/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import Sheaf.Paper.CompactSupportSiteCoherence
import Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.GlobalFiniteLevelCompactSupportBaseChange
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients

/-!
# Finite etale dualizing normalization

Source: main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-etale-locality.proof.md, Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization).

We use the canonical etale-origin coordinates of the finite etale normalization. The
functor rho is constructed by adjunction
conjugacy from the graph-normalized proper-support comparison. Its value eta on the
unit, the compositor c, theta, beta, sigma and E are specified constructions, never
fields that can be filled with unrelated endpoint isomorphisms. Equations are tested
on every etale representative whose comparison image belongs to pro-etale Dctf.
Full faithfulness, and the canonical tensor/pullback/unit/support comparisons, identify
these with the named pro-etale maps; naturality makes them independent of origins.

## Main definitions and statement

* `FiniteEtaleNormalization.rho` and `.eta`: the counit-normalized etale comparisons.
* `FiniteEtaleNormalization.comp`, `.sigma`, `.sourceEtale`, `.beta`: the specified maps.
* `FiniteEtaleDualizingNormalization`: their normalization and compatibility equations.
* `finite_etale_dualizing_normalization`: all these equations hold.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.FiniteEtaleNormalization

/-- Finiteness of the actual coefficient quotient A = O_E/varpi_E^n, including its size lift.
Source: main-20261015, etale-locality Step 1, the finite coefficient datum of
def-pur-conventions (blueprint: lem-pur-finite-etale-dualizing-normalization).
This local instance inlines the finite-coefficient construction recorded with
def-pur-co-smoothness, so the item does not import that legacy comparison module.
-/
noncomputable instance coefficientFinite (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  letI : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

/-- The coefficient unit in the same monoidal instance used by `derivedTensor`.
Source: main-20261015, etale-locality Step 1, the coefficient complex Lambda
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
abbrev coefficientUnit
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u}) :
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) := 𝟙_ _

/-- Tensoring the specified unit comparison and then applying the left unitor.
Assemble this map before coefficient specialization so that the tensor and unit share
one monoidal instance. Source: main-20261015, etale-locality Step 1, clause (1)
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def tensorUnitMap
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})
    (M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (a : M ≅ coefficientUnit A X) :
    ((Etale.derivedTensor A X).obj M).obj N ⟶ N :=
  ((Etale.derivedTensor A X).map a.hom).app N ≫
    (Etale.derivedTensorLeftUnitor A X N).hom

variable (P : WeilConjectures.PurityFiniteSetting.{u})
/-- The fixed Nagata compactification interface; no absolute separatedness is required.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
abbrev compactification
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    : HasCompactification f :=
  letI := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  letI := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  (HasCompactification.compactification f).hasCompactification

/-- The existing etale exceptional functor, with its compactification supplied internally.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
abbrev exceptional
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Etale.DerivedCategoryModule P.Coefficient Y ⥤
      Etale.DerivedCategoryModule P.Coefficient X :=
  letI := compactification P f
  Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f

/-- The existing compact-support functor, in the same supplied compactification.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def lower
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Etale.DerivedCategoryModule P.Coefficient X ⥤
      Etale.DerivedCategoryModule P.Coefficient Y :=
  letI := compactification P f
  Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f

/-- The existing exceptional counit, with the same supplied compactification.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def counit
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    exceptional P f ⋙ lower P f ⟶ 𝟭 _ :=
  letI := compactification P f
  (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) f).counit

/-- The canonical derived restriction in the same coefficient coordinates.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor

/-- The dualizing object is the unit value of the existing exceptional functor.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
abbrev omega
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Etale.DerivedCategoryModule P.Coefficient X :=
  letI := compactification P f
  Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) f

/-- The specified counit mate theta in omega-first order, as in the published API.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def tensorMap
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (K : Etale.DerivedCategoryModule P.Coefficient Y) :
    ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj
      (omega P f)).obj ((pull P f).obj K) ⟶ (exceptional P f).obj K :=
  letI := compactification P f
  Etale.dualizingComplexTensorMap P.Coefficient f K

/-- Extract the uniquely graph-normalized support comparison before specializing the
coefficient ring. Both the sheaf graph equation and its homotopy descent are retained
in the source existence statement, so its comparison is uniquely determined.
Source: lem-pur-etale-support-map-compatibility, normalization clauses
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def graphSupportModel (A : Type (u + 1)) [CommRing A] [Finite A] :
    ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
      [IsLocallyNoetherian T] [CompactSpace T]
      (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
      (c : Compactification e),
      Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
        (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory :=
  (Etale.etaleSupportMapCompatibility A).choose_spec.choose

/-- The canonical proper-support/sum comparison. The graph-extension equation and
homotopy-representative normalization in `etaleSupportMapCompatibility` determine the
chosen comparison uniquely: this choice is of the specified map, not an arbitrary iso.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def support
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (e : X ⟶ Y) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e] :
    lower P e ≅
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} P.Coefficient) e
        inferInstance).mapDerivedCategory :=
  letI := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of P.field.k))
  letI := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of P.field.k))
  letI := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  letI := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  letI := compactification P e
  (Etale.rightDerivedLowerShriekIso P.Coefficient
      (HasCompactification.compactification e)).symm ≪≫
    graphSupportModel P.Coefficient e
      (HasCompactification.compactification e)

/-- The unique counit-preserving comparison: conjugate of inverse proper-support/sum,
then the inverse exact-to-left-derived restriction comparison. No purity is used.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def rho
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (e : X ⟶ Y) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e] :
    exceptional P e ≅ pull P e :=
  letI := compactification P e
  conjugateIsoEquiv
      (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) e)
      ((Etale.etaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) e inferInstance).mapDerivedCategoryAdjunction)
      (support P e).symm ≪≫
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} P.Coefficient) e).symm

/-- Eta is rho at the coefficient unit followed by the canonical pullback-unit iso.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def eta
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (e : X ⟶ Y) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e] :
    omega P e ≅ coefficientUnit (ModuleCat.{u + 1} P.Coefficient) X :=
  (rho P e).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
    Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) e

/-- The exceptional compositor is precisely the conjugate of the specified
compact-support compositor, whose origin transport is `originCompositionModel`.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def comp
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :
    exceptional P (f ≫ g) ≅ exceptional P g ⋙ exceptional P f :=
  letI := compactification P f
  letI := compactification P g
  letI := compactification P (f ≫ g)
  conjugateIsoEquiv
    (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) (f ≫ g))
    ((Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) f).comp
      (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) g))
    (Etale.unboundedEtaleLowerShriekCompIso P.Coefficient f g)

/-- Canonical exceptional comparison for equal composites, by conjugacy of support
congruence. This inserts only the equality of morphisms in a Cartesian square.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def congr
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : X ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (w : f = g) :
    exceptional P f ≅ exceptional P g :=
  letI := compactification P f
  letI := compactification P g
  conjugateIsoEquiv
    (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) f)
    (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) g)
    (Etale.unboundedEtaleLowerShriekCongr P.Coefficient w.symm)

/-- Sigma is the specified tensor mate followed by inverse exceptional composition.
The coefficient category is fixed before any specialization, preserving its unit instance.
Source: main-20261015, etale-locality Step 1, definition of sigma
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def sigma
    (A : Type v) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
    {FC : A → A → Type w} {CC : A → Type (u + 1)}
    [∀ (M N : A), FunLike (FC M N) (CC M) (CC N)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [cf : HasCompactification f] [cg : HasCompactification g]
    [cfg : HasCompactification (f ≫ g)]
    [(Etale.rightDerivedLowerShriek A f).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek A g).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek A (f ≫ g)).IsLeftAdjoint]
    [IsIso (Etale.projectionMap A f)]
    (c : Etale.rightDerivedUpperShriek A (f ≫ g) ≅
      Etale.rightDerivedUpperShriek A g ⋙ Etale.rightDerivedUpperShriek A f) :=
  Etale.dualizingComplexTensorMapOfIsIso f (Etale.dualizingComplex A g) ≫
    c.inv.app (𝟙_ _)

/-- The tensor normalization equation, assembled with one abstract coefficient
category before specialization. The comparison argument is the actual rho, and its
unit component is eta. Source: main-20261015, etale-locality Step 1, clause (1)
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def tensorUnitEquation
    (A : Type v) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
    {FC : A → A → Type w} {CC : A → Type (u + 1)}
    [∀ (M N : A), FunLike (FC M N) (CC M) (CC N)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}} (e : X ⟶ Y) [ce : HasCompactification e]
    [(Etale.rightDerivedLowerShriek A e).IsLeftAdjoint]
    [IsIso (Etale.projectionMap A e)]
    (r : Etale.rightDerivedUpperShriek A e ≅ (Etale.upperStar A e).leftDerivedFunctor)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) : Prop :=
  Etale.dualizingComplexTensorMapOfIsIso e K ≫ r.hom.app K =
    tensorUnitMap A X (Etale.dualizingComplex A e)
      ((Etale.upperStar A e).leftDerivedFunctor.obj K)
      (r.app (coefficientUnit A Y) ≪≫ Etale.leftDerivedUpperStarUnitIso A e)

/-- The source-etale sigma equation with its actual compositor and rho supplied.
The left side expands E as c at the unit followed by rho at omega_h. Source:
main-20261015, etale-locality Step 1, clause (3)
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def sourceEtaleEquation
    (A : Type v) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
    {FC : A → A → Type w} {CC : A → Type (u + 1)}
    [∀ (M N : A), FunLike (FC M N) (CC M) (CC N)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y Z : Scheme.{u}} (e : X ⟶ Y) (h : Y ⟶ Z)
    [ce : HasCompactification e] [ch : HasCompactification h]
    [ceh : HasCompactification (e ≫ h)]
    [(Etale.rightDerivedLowerShriek A e).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek A h).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek A (e ≫ h)).IsLeftAdjoint]
    [IsIso (Etale.projectionMap A e)]
    (r : Etale.rightDerivedUpperShriek A e ≅ (Etale.upperStar A e).leftDerivedFunctor)
    (c : Etale.rightDerivedUpperShriek A (e ≫ h) ≅
      Etale.rightDerivedUpperShriek A h ⋙ Etale.rightDerivedUpperShriek A e) : Prop :=
  sigma A e h c ≫ c.hom.app (coefficientUnit A Z) ≫
      r.hom.app (Etale.dualizingComplex A h) =
    tensorUnitMap A X (Etale.dualizingComplex A e)
      ((Etale.upperStar A e).leftDerivedFunctor.obj (Etale.dualizingComplex A h))
      (r.app (coefficientUnit A Y) ≪≫ Etale.leftDerivedUpperStarUnitIso A e)

/-- The source-etale comparison E is c at the unit followed by rho at omega_h.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def sourceEtale
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (e : X ⟶ Y) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    (h : Y ⟶ Z) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h] :
    omega P (e ≫ h) ≅ (pull P e).obj (omega P h) :=
  (comp P e h).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
    (rho P e).app (omega P h)

/-- The specified exceptional base-change natural transformation, with both
compactifications supplied from the given finite-type field setting.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def baseChange
    {X Y X₁ Y₁ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (f₁ : X₁ ⟶ Y₁) [f₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated f₁] [LocallyOfFiniteType f₁] [QuasiCompact f₁]
    (g : Y₁ ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (g₁ : X₁ ⟶ X) [g₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated g₁] [LocallyOfFiniteType g₁] [QuasiCompact g₁]
    (sq : IsPullback g₁ f₁ f g) :
    exceptional P f ⋙ pull P g₁ ⟶ pull P g ⋙ exceptional P f₁ :=
  letI := compactification P f
  letI := compactification P f₁
  Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq

/-- The specified dualizing base-change mate beta, including the pullback-unit map.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def beta
    {X Y X₁ Y₁ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (f₁ : X₁ ⟶ Y₁) [f₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated f₁] [LocallyOfFiniteType f₁] [QuasiCompact f₁]
    (g : Y₁ ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (g₁ : X₁ ⟶ X) [g₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated g₁] [LocallyOfFiniteType g₁] [QuasiCompact g₁]
    (sq : IsPullback g₁ f₁ f g) :
    (pull P g₁).obj (omega P f) ⟶ omega P f₁ :=
  (baseChange P f f₁ g g₁ sq).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≫
    (exceptional P f₁).map
      (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) g).hom

/-- The target unit identification, assembled from rho at the unit, the canonical
pullback-unit comparisons and the tensor right unitor, before specialization.
Source: main-20261015, etale-locality Step 1, coefficient-unit identifications
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def targetUnit
    (A : Type v) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
    {FC : A → A → Type w} {CC : A → Type (u + 1)}
    [∀ (M N : A), FunLike (FC M N) (CC M) (CC N)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ⟶ Z)
    [cf : HasCompactification f] [ce : HasCompactification e]
    [(Etale.rightDerivedLowerShriek A f).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek A e).IsLeftAdjoint]
    (r : Etale.rightDerivedUpperShriek A e ≅ (Etale.upperStar A e).leftDerivedFunctor) :=
  ((Etale.derivedTensor A X).obj (Etale.dualizingComplex A f)).mapIso
      ((Etale.upperStar A f).leftDerivedFunctor.mapIso
          (r.app (𝟙_ _) ≪≫ Etale.leftDerivedUpperStarUnitIso A e) ≪≫
        Etale.leftDerivedUpperStarUnitIso A f) ≪≫
    Etale.derivedTensorRightUnitor A X (Etale.dualizingComplex A f)

/-- The canonical exceptional identity identification, conjugate of support identity.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def exceptionalId
    {X : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] :
    exceptional P (𝟙 X) ≅ 𝟭 (Etale.DerivedCategoryModule P.Coefficient X) :=
  letI := compactification P (𝟙 X)
  conjugateIsoEquiv
    (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) (𝟙 X))
    (Adjunction.id : (𝟭 (Etale.DerivedCategoryModule P.Coefficient X)) ⊣ 𝟭 _)
    (Etale.unboundedEtaleLowerShriekId P.Coefficient X).symm

/-- The canonical identity identification for derived pullback.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def pullId (X : Scheme.{u}) :
    pull P (𝟙 X) ≅ 𝟭 (Etale.DerivedCategoryModule P.Coefficient X) :=
  Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} P.Coefficient) (𝟙 X) ≪≫
    Functor.mapDerivedCategoryNatIso (Etale.upperStarId (ModuleCat.{u + 1} P.Coefficient) X) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Test the original pro-etale Dctf domain on all etale-origin representatives.
This is the domain convention of def-pur-co-smoothness, with no separatedness added.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def domain (X : Scheme.{u})
    (K : Etale.DerivedCategoryModule P.Coefficient X) : Prop :=
  ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) X
    ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj K)

end AlgebraicGeometry.ProEtale.FiniteEtaleNormalization

namespace AlgebraicGeometry.ProEtale

open FiniteEtaleNormalization

namespace FiniteEtaleNormalization.Laws

/-- The counit uniquely normalizes rho, on every object of the original domain.
Source: main-20261015, etale-locality Step 1, the corresponding displayed identity
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def Counit
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop :=
  ∀ (K : Etale.DerivedCategoryModule P.Coefficient X), domain P X K →
    (support P e).hom.app ((exceptional P e).obj K) ≫
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} P.Coefficient) e
        inferInstance).mapDerivedCategory.map
        ((rho P e).hom.app K ≫
          (Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} P.Coefficient) e).hom.app K) ≫
      ((Etale.etaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) e
          inferInstance).mapDerivedCategoryAdjunction).counit.app K =
        (FiniteEtaleNormalization.counit P e).app K

/-- Clause (1) in the published omega-first tensor order (the node uses symmetry).
Source: main-20261015, etale-locality Step 1, the corresponding displayed identity
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def TensorUnit
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop :=
  ∀ (K : Etale.DerivedCategoryModule P.Coefficient X), domain P X K →
    tensorUnitEquation (ModuleCat.{u + 1} P.Coefficient) e
      (ce := compactification P e) (rho P e) K

/-- Clause (2), identity, with both canonical identity comparisons inserted.
Source: main-20261015, etale-locality Step 1, the corresponding displayed identity
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def Identity
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop :=
  ∀ (K : Etale.DerivedCategoryModule P.Coefficient X), domain P X K →
    (rho P (𝟙 X)).hom.app K ≫ (pullId P X).hom.app K =
      (exceptionalId P).hom.app K

/-- Clause (2), actual rho composition, not merely pullback composition.
Source: main-20261015, etale-locality Step 1, the corresponding displayed identity
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def Composition
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop :=
  ∀
    {T : Scheme.{u}}
    [T.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (v : X ⟶ T) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    [Etale v]
    (K : Etale.DerivedCategoryModule P.Coefficient T), domain P T K →
    (rho P (e ≫ v)).hom.app K ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) e v).hom.app K =
      (comp P e v).hom.app K ≫ (rho P e).hom.app ((exceptional P v).obj K) ≫
        (pull P e).map ((rho P v).hom.app K)

/-- Clause (2), eta under every allowed Cartesian change of base.
Source: main-20261015, etale-locality Step 1, the corresponding displayed identity
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def EtaBaseChange
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop :=
  ∀
    {U₁ X₁ : Scheme.{u}}
    [U₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (U₁ ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    (e₁ : U₁ ⟶ X₁) [e₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated e₁] [LocallyOfFiniteType e₁] [QuasiCompact e₁]
    [Etale e₁]
    (w : X₁ ⟶ X) [w.IsOver (Spec (.of P.field.k))]
    [IsSeparated w] [LocallyOfFiniteType w] [QuasiCompact w]
    (w₁ : U₁ ⟶ U) [w₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated w₁] [LocallyOfFiniteType w₁] [QuasiCompact w₁]
    (sq : IsPullback w₁ e₁ e w),
    beta P e e₁ w w₁ sq ≫ (eta P e₁).hom =
      (pull P w₁).map (eta P e).hom ≫
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) w₁).hom

/-- Clause (3), E sigma is exactly tensoring eta with the identity.
Source: main-20261015, etale-locality Step 1, the corresponding displayed identity
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def SourceEtale
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop :=
  ∀
    {S : Scheme.{u}}
    [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    (h : X ⟶ S) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [Smooth h]
    , sourceEtaleEquation (ModuleCat.{u + 1} P.Coefficient) e h
        (ce := compactification P e) (ch := compactification P h)
        (ceh := compactification P (e ≫ h)) (rho P e) (comp P e h)

/-- The sigma inverse in clause (3) exists for this particular canonical map.
Source: main-20261015, etale-locality Step 1, the corresponding displayed identity
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def TargetSigmaIsIso
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop :=
  ∀
    {R R₁ : Scheme.{u}}
    [R.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (R ↘ Spec (.of P.field.k))]
    [QuasiCompact (R ↘ Spec (.of P.field.k))]
    [R₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (R₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (R₁ ↘ Spec (.of P.field.k))]
    (h : R ⟶ X) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [Smooth h]
    (h₁ : R₁ ⟶ U) [h₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁] [LocallyOfFiniteType h₁] [QuasiCompact h₁]
    [Smooth h₁]
    (e₁ : R₁ ⟶ R) [e₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated e₁] [LocallyOfFiniteType e₁] [QuasiCompact e₁]
    [Etale e₁]
    (_sq : IsPullback e₁ h₁ h e), IsIso (sigma (ModuleCat.{u + 1} P.Coefficient) h₁ e
        (cf := compactification P h₁) (cg := compactification P e)
        (cfg := compactification P (h₁ ≫ e)) (comp P h₁ e))

/-- Clause (3), inverse-free form of beta = sigma inverse composed with E inverse.
`targetUnit.inv` inserts exactly the target identification via eta_e.
Source: main-20261015, etale-locality Step 1, the corresponding displayed identity
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def SmoothBaseChange
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop :=
  ∀
    {R R₁ : Scheme.{u}}
    [R.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (R ↘ Spec (.of P.field.k))]
    [QuasiCompact (R ↘ Spec (.of P.field.k))]
    [R₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (R₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (R₁ ↘ Spec (.of P.field.k))]
    (h : R ⟶ X) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [Smooth h]
    (h₁ : R₁ ⟶ U) [h₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁] [LocallyOfFiniteType h₁] [QuasiCompact h₁]
    [Smooth h₁]
    (e₁ : R₁ ⟶ R) [e₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated e₁] [LocallyOfFiniteType e₁] [QuasiCompact e₁]
    [Etale e₁]
    (sq : IsPullback e₁ h₁ h e),
    beta P h h₁ e e₁ sq ≫ (targetUnit (ModuleCat.{u + 1} P.Coefficient) h₁ e
        (cf := compactification P h₁) (ce := compactification P e) (rho P e)).inv ≫
      sigma (ModuleCat.{u + 1} P.Coefficient) h₁ e
        (cf := compactification P h₁) (cg := compactification P e)
        (cfg := compactification P (h₁ ≫ e)) (comp P h₁ e) =
      (sourceEtale P e₁ h).inv ≫ (congr P (e₁ ≫ h) (h₁ ≫ e) sq.w).hom.app
        (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _)

/-- Genuine open restriction: compare rho on the pulled-back map with restricted rho,
through the specified exceptional base change and the canonical pullback square.
Source: main-20261015, etale-locality Step 1, the corresponding displayed identity
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def OpenRestriction
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop :=
  ∀
    {U₁ X₁ : Scheme.{u}}
    [U₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (U₁ ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    (e₁ : U₁ ⟶ X₁) [e₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated e₁] [LocallyOfFiniteType e₁] [QuasiCompact e₁]
    [Etale e₁]
    (j : X₁ ⟶ X) [j.IsOver (Spec (.of P.field.k))]
    [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (j₁ : U₁ ⟶ U) [j₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated j₁] [LocallyOfFiniteType j₁] [QuasiCompact j₁]
    [IsOpenImmersion j] [IsOpenImmersion j₁]
    (sq : IsPullback j₁ e₁ e j)
    (K : Etale.DerivedCategoryModule P.Coefficient X), domain P X K →
    (baseChange P e e₁ j j₁ sq).app K ≫ (rho P e₁).hom.app ((pull P j).obj K) =
      (pull P j₁).map ((rho P e).hom.app K) ≫
        Etale.derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} P.Coefficient) sq.toCommSq K

end FiniteEtaleNormalization.Laws

/-- All clauses of finite etale normalization, in canonical etale-origin coordinates.
Each field is an equation of the specified morphisms. The final field compares the
restriction of rho with rho on the restricted square, using the actual exceptional
base-change mate and the canonical pullback square, rather than an endpoint iso.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
structure FiniteEtaleDualizingNormalization
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop where
  /-- The counit uniquely normalizes rho, on every object of the original domain. -/
  counit : FiniteEtaleNormalization.Laws.Counit P e
  /-- Clause (1) in the published omega-first tensor order (the node uses symmetry). -/
  tensor_unit : FiniteEtaleNormalization.Laws.TensorUnit P e
  /-- Clause (2), identity, with both canonical identity comparisons inserted. -/
  identity : FiniteEtaleNormalization.Laws.Identity P e
  /-- Clause (2), actual rho composition, not merely pullback composition. -/
  composition : FiniteEtaleNormalization.Laws.Composition P e
  /-- Clause (2), eta under every allowed Cartesian change of base. -/
  eta_base_change : FiniteEtaleNormalization.Laws.EtaBaseChange P e
  /-- Clause (3), E sigma is exactly tensoring eta with the identity. -/
  source_etale : FiniteEtaleNormalization.Laws.SourceEtale P e
  /-- The sigma inverse in clause (3) exists for this particular canonical map. -/
  target_sigma_iso : FiniteEtaleNormalization.Laws.TargetSigmaIsIso P e
  /-- Clause (3), inverse-free form of beta = sigma inverse composed with E inverse.
`targetUnit.inv` inserts exactly the target identification via eta_e. -/
  smooth_base_change : FiniteEtaleNormalization.Laws.SmoothBaseChange P e
  /-- Genuine open restriction: compare rho on the pulled-back map with restricted rho,
through the specified exceptional base change and the canonical pullback square. -/
  open_restriction : FiniteEtaleNormalization.Laws.OpenRestriction P e

/-- Finite etale dualizing normalization, with no orientation or Tate twist.

Proof (the nine steps of the DAG proof):
1. Finite-type schemes over the field are Noetherian. Exceptional inverse images
preserve Dctf. Constructible etale origins and fully faithful site comparison transport
the specified pullbacks, units, tensors and compact-support maps. Expand projection
into its proper counit mate and open tensor factor; the canonical comparison counit
and degreewise extension-by-zero formulas transport their actual transposes.
2. The exact sum/evaluation adjunction and the graph-normalized proper-support
comparison give rho as the conjugate of the inverse left-adjoint comparison. Its
counit equation characterizes it uniquely, and conjugating the inverse gives its
inverse. Evaluation at the unit defines eta with the coefficient-unit comparison.
3. Transpose rho theta and the proposed unit map. The normalized sum projection
sends (s,m) tensor k to (s,m tensor s*k); both transposes evaluate eta(m) against k.
This equality holds on tensor representatives and descends canonically, so the
adjunction bijection proves tensor_unit. No stalkwise detection of derived maps is used.
4. The proper-support compositor sends nested lift summands to their composite lift
and preserves evaluation. Conjugacy and composite-adjunction mate pasting give the
displayed rho composition equation and its identity normalization.
5. The actual compact-support exchange is the normalized sum exchange. Its conjugacy
equation preserves evaluation after coefficient-unit pullback; transpose under the
primed exceptional adjunction to obtain eta_base_change.
6. Substitute the definitions of E and sigma; cancel c with its inverse. Apply step 3
at omega_h and symmetry to obtain source_etale and invertibility of source sigma.
7. Theta at the coefficient unit is the unitor: the proper projection with unit is
identity and the open tensor factor is the unitor. Naturality at eta_e identifies
the normalized inverse of target sigma with Rhprime!(eta_e) followed by c.
8. In the etale-horizontal smooth square, expand the two composite counits. The
etale-horizontal-support-mate theorem identifies the support interchange with the
normalized sum exchange. Mate pasting gives equality of the two double-counit
composites for the candidate E inverse followed by target sigma inverse.
9. Cancel the sum/evaluation adjunction and then the primed exceptional adjunction.
The candidate is exactly the specified beta, yielding smooth_base_change and
target_sigma_iso. Exchange pasting and mate pasting give open_restriction. All
fields are quantified over the full setting, so the same equations hold on further
compatible open restrictions, with their rho identified by open_restriction.

Dependencies: lem-weil-pbc-finite-type-over-noetherian,
lem-sf-proetale-constructible-origin, thm-weil-pbc-site-comparison,
lem-weil-pbc-comparison-pullback, lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-pur-compact-support-site-coherence, thm-cbc-finite-level-proetale,
def-exchange-projection, lem-weil-pbc-comparison-direct-image-canonical-mate,
lem-cbc-proetale-extension-zero-comparison, lem-amb-etale-adjoint-locality,
lem-sfb-quasifinite-compact-support-exact, lem-pur-etale-support-map-compatibility,
def-weil-pbc-adjunction-conjugate, def-weil-pbc-composite-adjunction,
lem-weil-pbc-mate-pasting, def-weil-pbc-etale-shriek-base-change-map,
lem-weil-pbc-etale-shriek-base-change-modules, def-pur-co-smoothness,
lem-weil-pbc-ringed-projection-mate-exact, lem-pur-etale-horizontal-support-mate,
and fix-lem-exchanges.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
theorem finite_etale_dualizing_normalization
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : FiniteEtaleDualizingNormalization P e := by
  sorry

end AlgebraicGeometry.ProEtale
