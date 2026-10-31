/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses
public import WeilConjectures.AlgebraicGeometry.CondensedRationalAdjunction
public import WeilConjectures.AlgebraicGeometry.RationalLocalizedHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ScalarSixCompactSupport
public import WeilConjectures.SixFunctors.ScalarSixPullback
public import WeilConjectures.Algebra.Homology.OrdinaryLineDerivedScalarComparison
import WeilConjectures.AlgebraicGeometry.IntegralModels
public import WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison
public import WeilConjectures.AlgebraicGeometry.TransportIntegralCounitRealization
import WeilConjectures.AlgebraicGeometry.FieldShriekSystemComparison
import WeilConjectures.AlgebraicGeometry.CompactSupportStrictScalarMate
import WeilConjectures.CategoryTheory.StrictTowerArithmeticRestriction
import WeilConjectures.AlgebraicGeometry.CompactSupportCompletedScalarArrow
import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimitRealization
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower
import WeilConjectures.AlgebraicGeometry.CompactSupportProjectionRealization
import WeilConjectures.AlgebraicGeometry.CompactSupportScalarGammaIdentification
import WeilConjectures.AlgebraicGeometry.NativeIntegralReductionExchange
import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
import WeilConjectures.AlgebraicGeometry.CartesianCoefficientTwistsSupplement
import WeilConjectures.SixFunctors.ScalarSixTensorHom
import WeilConjectures.AlgebraicGeometry.IntegralOperationsScalarComparisonModels
import WeilConjectures.AlgebraicGeometry.NormalizedIntegralScalarPullbackComparison
import WeilConjectures.AlgebraicGeometry.LocalizedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.CohomologicalDimension
public import Mathlib.Order.WithBot
public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarSections

/-! # Native rational coefficient transport of the smooth adjunction

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.proof.md, (2)--(3)
(blueprint: lem-pur-native-rational-field-adjunction-transport).

Finite stages retain the integral-to-rational Hom formula of
`CondensedRationalAdjunction.Laws`. The top coefficient index denotes the
finite-subextension-valued condensed algebraic closure. It carries only the
compact-support and twisted-pullback functors and their endpoint comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeRationalFieldTransport

variable (ell : ℕ) [Fact ell.Prime]

/-- The finite rational coefficients together with their prescribed condensed closure.
Source: field-extension-towers (3) and its algebraic-closure endpoint
(blueprint: lem-pur-native-rational-field-adjunction-transport). -/
def coefficient : WithTop (PadicAlgCl.FiniteIntermediateField ell) → Coefficient ell
  | none => .closure
  | some E => .rational E

/-- The actual coefficient inclusion, including the finite-subextension-valued endpoint.
Source: field-extension-towers (3), native scalar extension
(blueprint: lem-pur-native-rational-field-adjunction-transport). -/
def inclusion : ∀ {E F : WithTop (PadicAlgCl.FiniteIntermediateField ell)}, E ≤ F →
    ((coefficient ell E).bundled.{u} ell ⟶ (coefficient ell F).bundled ell)
  | none, none, _ => 𝟙 _
  | some E, none, _ => ⟨⟨Profinite.padicSubfieldRingObjToPadicAlgCl ell E⟩⟩
  | some _, some _, h =>
      ⟨⟨Profinite.padicSubfieldRingObjMap ell (WithTop.coe_le_coe.mp h)⟩⟩
  | none, some _, h => False.elim (WithTop.not_top_le_coe _ h)

/-- The multiplication unitor on ordinary derived extension along the identity.
It is the conjugate of the literal restriction-of-scalars identity comparison.
Source: field-extension-towers (3), scalar unitors
(blueprint: lem-pur-native-rational-field-adjunction-transport). -/
def scalarUnitor (c : Coefficient ell) (T : Scheme.{u}) :
    scalarSixChange (𝟙 (c.bundled ell)) T ≅ 𝟭 (c.derived ell T) :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := c.obj ell) (𝟙 (c.obj ell)) T)).leftAdjointUniq
      (Adjunction.id.ofNatIsoRight
        (Functor.mapDerivedCategoryNatIso
          (Mod.comapCongr (coefficientMap_id (Λ := c.obj ell) T)) ≪≫
          Functor.mapDerivedCategoryNatIso (Mod.comapId (condensedRingObj (c.obj ell) T)) ≪≫
          Functor.mapDerivedCategoryIdIso _).symm)

/-- The literal restricted functors at all endpoints and the finite adjunctions.
The closure endpoint has no adjunction field. The main theorem quantifies over
this entire family, including its integral and rational adjunctions; none of these
adjunctions is chosen by its conclusion.
Source: field-extension-towers (3), P_B and H_B
(blueprint: lem-pur-native-rational-field-adjunction-transport). -/
structure Functors (D : WeilConjectures.FiniteFieldDatum.{u}) (s : SmoothDatum D) where
  support_closed : ∀ (E : WithTop (PadicAlgCl.FiniteIntermediateField ell)) K,
    property ell (coefficient ell E) s.X.left K →
      property ell (coefficient ell E) s.Y.left
        ((CondensedRing.rightDerivedLowerShriekOfCompactification
          ((coefficient ell E).obj ell) s.compactification).obj K)
  source_closed : ∀ (E : WithTop (PadicAlgCl.FiniteIntermediateField ell)) K,
    property ell (coefficient ell E) s.Y.left K →
      property ell (coefficient ell E) s.X.left
        (((coefficient ell E).smoothSource ell s.map s.dim).obj K)
  integral : ∀ E : PadicAlgCl.FiniteIntermediateField ell,
    ExplicitAdjunction ell D (.integral E) s
  rational : ∀ E : PadicAlgCl.FiniteIntermediateField ell,
    support ell (.rational E) s.compactification (support_closed E) ⊣
      source ell (.rational E) s.map s.dim (source_closed E)

variable {ell}

/-- The finite explicit adjunction with exactly the displayed restricted functors.
Source: rational-adjunction, the adjunction retained in field-extension-towers (3)
(blueprint: lem-pur-native-rational-field-adjunction-transport). -/
def Functors.finiteAdjunction {D : WeilConjectures.FiniteFieldDatum.{u}} {s : SmoothDatum D}
    (G : Functors ell D s) (E : PadicAlgCl.FiniteIntermediateField ell) :
    ExplicitAdjunction ell D (.rational E) s :=
  ⟨G.support_closed E, G.source_closed E, G.rational E⟩

/-- Compact support at a finite or algebraic-closure endpoint, using the same model.
Source: field-extension-towers (3), P
(blueprint: lem-pur-native-rational-field-adjunction-transport). -/
abbrev Functors.P {D : WeilConjectures.FiniteFieldDatum.{u}} {s : SmoothDatum D}
    (G : Functors ell D s) (E : WithTop (PadicAlgCl.FiniteIntermediateField ell)) :=
  support ell (coefficient ell E) s.compactification (G.support_closed E)

/-- Native pullback, positive Tate power and shift 2d at every endpoint.
Source: field-extension-towers (3), H
(blueprint: lem-pur-native-rational-field-adjunction-transport). -/
abbrev Functors.H {D : WeilConjectures.FiniteFieldDatum.{u}} {s : SmoothDatum D}
    (G : Functors ell D s) (E : WithTop (PadicAlgCl.FiniteIntermediateField ell)) :=
  source ell (coefficient ell E) s.map s.dim (G.source_closed E)

/-- Retain every finite Hom formula, including all integral models and all rational
morphisms, from the recorded rational adjunction. In particular the units and counits
below are those of these very adjunctions.
Source: field-extension-towers (3), rational-localized-hom and rational-adjunction
(blueprint: lem-pur-native-rational-field-adjunction-transport). -/
structure Rationalization {D : WeilConjectures.FiniteFieldDatum.{u}} {s : SmoothDatum D}
    (G : Functors ell D s) where
  localX : ∀ (E : PadicAlgCl.FiniteIntermediateField ell) K,
    property ell (.integral E) s.X.left K → property ell (.rational E) s.X.left
      ((scalarSixChange (CondensedRationalAdjunction.coefficientMap ell E) s.X.left).obj K)
  localY : ∀ (E : PadicAlgCl.FiniteIntermediateField ell) K,
    property ell (.integral E) s.Y.left K → property ell (.rational E) s.Y.left
      ((scalarSixChange (CondensedRationalAdjunction.coefficientMap ell E) s.Y.left).obj K)
  comparison : ∀ E : PadicAlgCl.FiniteIntermediateField ell,
    CondensedRationalAdjunction.Comparisons ell D E s (G.integral E) (G.finiteAdjunction E)
      (localX E) (localY E)
  laws : ∀ E : PadicAlgCl.FiniteIntermediateField ell,
    CondensedRationalAdjunction.Laws ell D E s (G.integral E) (G.finiteAdjunction E)
      (localX E) (localY E) (comparison E)

/-- The actual inclusion of continuous integral coefficient rings.
It condenses the existing valuation-ring inclusion, not a chosen ring map.
Source: field-extension-towers (1)--(2), O_E to O_F
(blueprint: lem-pur-native-rational-field-adjunction-transport). -/
def integralInclusion (ell : ℕ) [Fact ell.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) :
    (Coefficient.integral E).bundled.{u} ell ⟶ (Coefficient.integral F).bundled ell :=
  letI := PadicAlgCl.normedFieldOfAlgebra ell E.1
  letI := PadicAlgCl.normedFieldOfAlgebra ell F.1
  CommMon.homMk (Mon.Hom.mk
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
        (Profinite.continuousMapRingSheafMap (integersInclusion ell h)
          (continuous_integersInclusion ell h))))

/-- Ordinary integral scalar extension restricted by its membership certificate.
Source: field-extension-towers (1)--(2), C^T
(blueprint: lem-pur-native-rational-field-adjunction-transport). -/
def integralScalar (ell : ℕ) [Fact ell.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) (T : Scheme.{u})
    (preserves : ∀ K, property ell (.integral E) T K → property ell (.integral F) T
      ((scalarSixChange (integralInclusion ell h) T).obj K)) :
    (Coefficient.integral E).ctf ell T ⥤ (Coefficient.integral F).ctf ell T :=
  (property ell (.integral F) T).lift
    ((property ell (.integral E) T).ι ⋙ scalarSixChange (integralInclusion ell h) T)
    (fun K ↦ preserves K.obj K.property)

/-- The source's Step-1 integral normalization, on a supplied family of adjunctions.
The two isomorphisms are pinned to the native proper/open and pullback/Tate/shift
maps. The final fields are the exact integral unit and counit transport equations.
The trace-counit family satisfies this normalization by field-extension-towers (2)
and the native identifications in the node's proof Steps 1--5. The rational theorem
is universal in a family with this normalization, so cannot choose a different A0.
Source: field-extension-towers proof (2)--(3), before inverting ell
(blueprint: lem-pur-native-rational-field-adjunction-transport). -/
structure IntegralNormalization {D : WeilConjectures.FiniteFieldDatum.{u}}
    {s : SmoothDatum D} (G : Functors ell D s) where
  preservesX : ∀ {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) K,
    property ell (.integral E) s.X.left K → property ell (.integral F) s.X.left
      ((scalarSixChange (integralInclusion ell h) s.X.left).obj K)
  preservesY : ∀ {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) K,
    property ell (.integral E) s.Y.left K → property ell (.integral F) s.Y.left
      ((scalarSixChange (integralInclusion ell h) s.Y.left).obj K)
  integral_map : ∀ {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F),
    (Coefficient.integral E).integralMap ell ≫ (integralInclusion ell h).hom.hom =
      (Coefficient.integral F).integralMap ell
  line : ∀ {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F),
    ScalarLineCoordinates ell (integralInclusion ell h) (integral_map h) s.X.left
  b : ∀ {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F),
    support ell (.integral E) s.compactification (G.integral E).support_closed ⋙
        integralScalar ell h s.Y.left (preservesY h) ≅
      integralScalar ell h s.X.left (preservesX h) ⋙
        support ell (.integral F) s.compactification (G.integral F).support_closed
  a : ∀ {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F),
    source ell (.integral E) s.map s.dim (G.integral E).source_closed ⋙
        integralScalar ell h s.X.left (preservesX h) ≅
      integralScalar ell h s.Y.left (preservesY h) ⋙
        source ell (.integral F) s.map s.dim (G.integral F).source_closed
  b_normalized : ∀ {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F)
    (M : (Coefficient.integral E).ctf ell s.X.left),
    ((b h).hom.app M).hom =
      (scalarCompactSupportMap (integralInclusion ell h) s.compactification.i
        s.compactification.g).app M.obj
  a_normalized : ∀ {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F)
    (K : (Coefficient.integral E).ctf ell s.Y.left),
    ((a h).hom.app K).hom = sourceScalar ell (integralInclusion ell h) s.map s.dim
      (integral_map h) (line h) K.obj
  unit : ∀ {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F)
    (M : (Coefficient.integral E).ctf ell s.X.left),
    (G.integral F).adjunction.unit.app
        ((integralScalar ell h s.X.left (preservesX h)).obj M) =
      (integralScalar ell h s.X.left (preservesX h)).map
          ((G.integral E).adjunction.unit.app M) ≫
        (a h).hom.app
          ((support ell (.integral E) s.compactification (G.integral E).support_closed).obj M) ≫
        (source ell (.integral F) s.map s.dim (G.integral F).source_closed).map
          ((b h).hom.app M)
  counit : ∀ {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F)
    (K : (Coefficient.integral E).ctf ell s.Y.left),
    (b h).hom.app ((source ell (.integral E) s.map s.dim (G.integral E).source_closed).obj K) ≫
        (support ell (.integral F) s.compactification (G.integral F).support_closed).map
          ((a h).hom.app K) ≫
        (G.integral F).adjunction.counit.app
          ((integralScalar ell h s.Y.left (preservesY h)).obj K) =
      (integralScalar ell h s.Y.left (preservesY h)).map
        ((G.integral E).adjunction.counit.app K)

variable (ell)

/-- Restriction of the actual ordinary derived tensor functors to the named categories.
Identity, composition and Tate-line fields certify the specified inclusions; they
cannot replace them by arbitrary coefficient maps or arbitrary line automorphisms.
Source: field-extension-towers (3), scalar functors and their ordinary associators
(blueprint: lem-pur-native-rational-field-adjunction-transport). -/
structure Scalars (D : WeilConjectures.FiniteFieldDatum.{u}) (s : SmoothDatum D) where
  map_id : ∀ E : WithTop (PadicAlgCl.FiniteIntermediateField ell),
    inclusion.{u} ell (le_refl E) = 𝟙 _
  map_comp : ∀ {E F L : WithTop (PadicAlgCl.FiniteIntermediateField ell)}
    (h : E ≤ F) (j : F ≤ L), inclusion.{u} ell h ≫ inclusion ell j = inclusion ell (h.trans j)
  integral_map : ∀ {E F : WithTop (PadicAlgCl.FiniteIntermediateField ell)} (h : E ≤ F),
    (coefficient ell E).integralMap ell ≫ (inclusion.{u} ell h).hom.hom =
      (coefficient ell F).integralMap ell
  line : ∀ {E F : WithTop (PadicAlgCl.FiniteIntermediateField ell)} (h : E ≤ F),
    ScalarLineCoordinates ell (inclusion ell h) (integral_map h) s.X.left
  preservesX : ∀ {E F : WithTop (PadicAlgCl.FiniteIntermediateField ell)} (h : E ≤ F) K,
    property ell (coefficient ell E) s.X.left K →
      property ell (coefficient ell F) s.X.left
        ((scalarSixChange (inclusion ell h) s.X.left).obj K)
  preservesY : ∀ {E F : WithTop (PadicAlgCl.FiniteIntermediateField ell)} (h : E ≤ F) K,
    property ell (coefficient ell E) s.Y.left K →
      property ell (coefficient ell F) s.Y.left
        ((scalarSixChange (inclusion ell h) s.Y.left).obj K)

variable {ell}

/-- Ordinary derived scalar extension on X, restricted by membership alone.
Source: field-extension-towers (3), S^X
(blueprint: lem-pur-native-rational-field-adjunction-transport). -/
def Scalars.SX {D : WeilConjectures.FiniteFieldDatum.{u}} {s : SmoothDatum D}
    (S : Scalars ell D s) {E F : WithTop (PadicAlgCl.FiniteIntermediateField ell)}
    (h : E ≤ F) : (coefficient ell E).ctf ell s.X.left ⥤
      (coefficient ell F).ctf ell s.X.left :=
  (property ell (coefficient ell F) s.X.left).lift
    ((property ell (coefficient ell E) s.X.left).ι ⋙
      scalarSixChange (inclusion ell h) s.X.left) (fun K ↦ S.preservesX h K.obj K.property)

/-- Ordinary derived scalar extension on Y, restricted by membership alone.
Source: field-extension-towers (3), S^Y
(blueprint: lem-pur-native-rational-field-adjunction-transport). -/
def Scalars.SY {D : WeilConjectures.FiniteFieldDatum.{u}} {s : SmoothDatum D}
    (S : Scalars ell D s) {E F : WithTop (PadicAlgCl.FiniteIntermediateField ell)}
    (h : E ≤ F) : (coefficient ell E).ctf ell s.Y.left ⥤
      (coefficient ell F).ctf ell s.Y.left :=
  (property ell (coefficient ell F) s.Y.left).lift
    ((property ell (coefficient ell E) s.Y.left).ι ⋙
      scalarSixChange (inclusion ell h) s.Y.left) (fun K ↦ S.preservesY h K.obj K.property)

/-- The prescribed ambient scalar associator, followed only by coefficient-map equality.
Source: field-extension-towers (3), c^T
(blueprint: lem-pur-native-rational-field-adjunction-transport). -/
def Scalars.associator {D : WeilConjectures.FiniteFieldDatum.{u}} {s : SmoothDatum D}
    (S : Scalars ell D s) {E F L : WithTop (PadicAlgCl.FiniteIntermediateField ell)}
    (h : E ≤ F) (j : F ≤ L) (T : Scheme.{u}) :
    scalarSixChange (inclusion ell h) T ⋙ scalarSixChange (inclusion ell j) T ≅
      scalarSixChange (inclusion ell (h.trans j)) T :=
  scalarSixTower (inclusion ell h) (inclusion ell j) T ≪≫
    eqToIso (congrArg
      (fun a : (coefficient ell E).bundled ell ⟶ (coefficient ell L).bundled ell ↦
        scalarSixChange a T) (S.map_comp h j))

/-- The prescribed ambient scalar unitor, after coefficient-map equality.
Source: field-extension-towers (3), identity coefficients
(blueprint: lem-pur-native-rational-field-adjunction-transport). -/
def Scalars.unitor {D : WeilConjectures.FiniteFieldDatum.{u}} {s : SmoothDatum D}
    (S : Scalars ell D s) (E : WithTop (PadicAlgCl.FiniteIntermediateField ell))
    (T : Scheme.{u}) :
    scalarSixChange (inclusion ell (le_refl E)) T ≅ 𝟭 ((coefficient ell E).derived ell T) :=
  eqToIso (congrArg (fun a ↦ scalarSixChange a T) (S.map_id E)) ≪≫
    scalarUnitor ell (coefficient ell E) T

/-- The two endpoint isomorphisms, with actual-map normalizations, and the scalar
associators and unitors restricted from ordinary derived tensor. Naturality is built
into these natural isomorphisms, including for arbitrary rational morphisms.
Source: field-extension-towers (3), a, b and c
(blueprint: lem-pur-native-rational-field-adjunction-transport). -/
structure Comparisons {D : WeilConjectures.FiniteFieldDatum.{u}} {s : SmoothDatum D}
    (G : Functors ell D s) (S : Scalars ell D s) where
  b : ∀ {E F : WithTop (PadicAlgCl.FiniteIntermediateField ell)} (h : E ≤ F),
    G.P E ⋙ S.SY h ≅ S.SX h ⋙ G.P F
  a : ∀ {E F : WithTop (PadicAlgCl.FiniteIntermediateField ell)} (h : E ≤ F),
    G.H E ⋙ S.SX h ≅ S.SY h ⋙ G.H F
  b_normalized : ∀ {E F : WithTop (PadicAlgCl.FiniteIntermediateField ell)} (h : E ≤ F)
    (M : (coefficient ell E).ctf ell s.X.left),
    ((b h).hom.app M).hom =
      (scalarCompactSupportMap (inclusion ell h) s.compactification.i
        s.compactification.g).app M.obj
  a_normalized : ∀ {E F : WithTop (PadicAlgCl.FiniteIntermediateField ell)} (h : E ≤ F)
    (K : (coefficient ell E).ctf ell s.Y.left),
    ((a h).hom.app K).hom = sourceScalar ell (inclusion ell h) s.map s.dim
      (S.integral_map h) (S.line h) K.obj
  cX : ∀ {E F L : WithTop (PadicAlgCl.FiniteIntermediateField ell)} (h : E ≤ F) (j : F ≤ L),
    S.SX h ⋙ S.SX j ≅ S.SX (h.trans j)
  cY : ∀ {E F L : WithTop (PadicAlgCl.FiniteIntermediateField ell)} (h : E ≤ F) (j : F ≤ L),
    S.SY h ⋙ S.SY j ≅ S.SY (h.trans j)
  cX_normalized : ∀ {E F L : WithTop (PadicAlgCl.FiniteIntermediateField ell)}
    (h : E ≤ F) (j : F ≤ L) (M : (coefficient ell E).ctf ell s.X.left),
    ((cX h j).hom.app M).hom = (S.associator h j s.X.left).hom.app M.obj
  cY_normalized : ∀ {E F L : WithTop (PadicAlgCl.FiniteIntermediateField ell)}
    (h : E ≤ F) (j : F ≤ L) (K : (coefficient ell E).ctf ell s.Y.left),
    ((cY h j).hom.app K).hom = (S.associator h j s.Y.left).hom.app K.obj
  uX : ∀ E : WithTop (PadicAlgCl.FiniteIntermediateField ell), S.SX (le_refl E) ≅ 𝟭 _
  uY : ∀ E : WithTop (PadicAlgCl.FiniteIntermediateField ell), S.SY (le_refl E) ≅ 𝟭 _
  uX_normalized : ∀ (E : WithTop (PadicAlgCl.FiniteIntermediateField ell))
    (M : (coefficient ell E).ctf ell s.X.left),
    ((uX E).hom.app M).hom = (S.unitor E s.X.left).hom.app M.obj
  uY_normalized : ∀ (E : WithTop (PadicAlgCl.FiniteIntermediateField ell))
    (K : (coefficient ell E).ctf ell s.Y.left),
    ((uY E).hom.app K).hom = (S.unitor E s.Y.left).hom.app K.obj

/-- All four displayed equations and both identity-coefficient equations, on the same
native functors and maps. The two cocycles include finite-to-closure extensions; the
adjunction equations quantify only over finite fields. Pasting these equations is
exactly unital and transitive transport of the adjunctions.
Source: field-extension-towers (3), displayed identities and endpoint coherence
(blueprint: lem-pur-native-rational-field-adjunction-transport). -/
structure Laws {D : WeilConjectures.FiniteFieldDatum.{u}} {s : SmoothDatum D}
    (G : Functors ell D s) (S : Scalars ell D s) (C : Comparisons G S) : Prop where
  unit : ∀ {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F)
    (M : (Coefficient.rational E).ctf ell s.X.left),
    (G.rational F).unit.app ((S.SX (WithTop.coe_le_coe.mpr h)).obj M) =
      (S.SX (WithTop.coe_le_coe.mpr h)).map ((G.rational E).unit.app M) ≫
        (C.a (WithTop.coe_le_coe.mpr h)).hom.app ((G.P E).obj M) ≫
          (G.H F).map ((C.b (WithTop.coe_le_coe.mpr h)).hom.app M)
  counit : ∀ {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F)
    (K : (Coefficient.rational E).ctf ell s.Y.left),
    (C.b (WithTop.coe_le_coe.mpr h)).hom.app ((G.H E).obj K) ≫
        (G.P F).map ((C.a (WithTop.coe_le_coe.mpr h)).hom.app K) ≫
          (G.rational F).counit.app ((S.SY (WithTop.coe_le_coe.mpr h)).obj K) =
      (S.SY (WithTop.coe_le_coe.mpr h)).map ((G.rational E).counit.app K)
  support_cocycle : ∀ {E F L : WithTop (PadicAlgCl.FiniteIntermediateField ell)}
    (h : E ≤ F) (j : F ≤ L) (M : (coefficient ell E).ctf ell s.X.left),
    (S.SY j).map ((C.b h).hom.app M) ≫
        (C.b j).hom.app ((S.SX h).obj M) ≫ (G.P L).map ((C.cX h j).hom.app M) =
      (C.cY h j).hom.app ((G.P E).obj M) ≫ (C.b (h.trans j)).hom.app M
  source_cocycle : ∀ {E F L : WithTop (PadicAlgCl.FiniteIntermediateField ell)}
    (h : E ≤ F) (j : F ≤ L) (K : (coefficient ell E).ctf ell s.Y.left),
    (S.SX j).map ((C.a h).hom.app K) ≫
        (C.a j).hom.app ((S.SY h).obj K) ≫ (G.H L).map ((C.cY h j).hom.app K) =
      (C.cX h j).hom.app ((G.H E).obj K) ≫ (C.a (h.trans j)).hom.app K
  support_unit : ∀ (E : WithTop (PadicAlgCl.FiniteIntermediateField ell))
    (M : (coefficient ell E).ctf ell s.X.left),
    (C.b (le_refl E)).hom.app M ≫ (G.P E).map ((C.uX E).hom.app M) =
      (C.uY E).hom.app ((G.P E).obj M)
  source_unit : ∀ (E : WithTop (PadicAlgCl.FiniteIntermediateField ell))
    (K : (coefficient ell E).ctf ell s.Y.left),
    (C.a (le_refl E)).hom.app K ≫ (G.H E).map ((C.uY E).hom.app K) =
      (C.uX E).hom.app ((G.H E).obj K)

/-- Normalized endpoint isomorphisms and transport equations for the supplied
finite rational adjunctions. The conclusion contains no new adjunction data.
Source: field-extension-towers (3), including the endpoint cocycle paragraph
(blueprint: lem-pur-native-rational-field-adjunction-transport). -/
structure Result {D : WeilConjectures.FiniteFieldDatum.{u}} {s : SmoothDatum D}
    (G : Functors ell D s) where
  scalars : Scalars ell D s
  comparisons : Comparisons G scalars
  laws : Laws G scalars comparisons

/-- Native rational adjunctions transport along finite coefficient inclusions, with
coherent endpoint comparisons also at the algebraic closure, where no adjunction is
asserted. Source: latest blueprint, field-extension-towers proof (2)--(3)
(blueprint: lem-pur-native-rational-field-adjunction-transport).

Proof. 1. Use the supplied integral adjunctions and their exact native unit and
counit transport equations in IntegralNormalization. For the trace-counit family
these are obtained by transport-integral-counit-realization. Finite-free ordinary
scalar extension agrees with completed extension via its augmentation-normalized
comparison; conjugate the integral unit and counit equations by that comparison.
2. Field-shriek-system-comparison identifies the entire support-system mate with
the proper/open strict scalar mate. Arithmetic restriction preserves quotient
augmentations when ell powers are replaced by uniformizer powers.
3. Complete-compactification-limit-realization has the actual quotient projections.
Finite Tor amplitude bounds the reduction towers below; the integral direct-image
bound controls the output. Projection-realization and scalar-gamma-identification
therefore identify the realized support arrow with the native proper/open mate.
4. Use native-integral-reduction-exchange and finite-native-tate-source-comparison.
Successive quotient associativity, cartesian coefficients and scalar tensor
comparison identify the finite balanced pullback generator map. Its normalized
uniqueness identifies the realized pullback map with the native comparison.
5. In a common root frame the line maps are multiplication; ordinary-line-derived-
scalar-comparison retains this normalization for powers, evaluation and shift,
including d=0. Thus the whole source comparison is the native one.
6. Localized-direct-image-comparison identifies the proper localization mate;
compose with open balancing. Rational-localized-hom supplies exactly the support
and pullback endpoints. The Tate line and shift maps use the same coefficient unit.
7. Scalar-six coefficient composition on O_E to O_F to F and O_E to E to F gives
the two localization squares, with the ordinary tensor associator retained.
8. On a localized integral model, expand the rational unit using
CondensedRationalAdjunction.Laws.unit, substitute integral transport, and move the
localization support map past the source comparison by naturality. The resulting
expression is exactly the rational unit formula at E followed by a and H_F(b).
9. For the counit precompose with localization of P_E(u_E) followed by v_E.
Naturality and the two localization squares reduce the equation to the integral
counit equation. Cancel this specified isomorphism to obtain the rational equation.
10. Rational-localized-hom supplies models for every object. Conjugate by every
model identification; rational-adjunction gives independence and naturality for
all rational morphisms, not only integral arrows.
11. Native proper/open coefficient composition gives the support cocycle and
unitors, also for finite-to-closure coefficients. The algebraically closed base
has ell-cohomological dimension zero, as required by scalar-six-compact-support.
12. Pullback coefficient coherence and the ordinary line cocycle give the source
cocycle and unitors. At the closure use the finite-subextension-valued Tate line;
only its functor and comparisons are needed.
13. Paste successive unit and counit equations. Naturality moves the middle source
and support factors past each other, and the two cocycles combine them into the
direct comparison. For identities the scalar unitors cancel. -/
theorem native_rational_field_adjunction_transport
    (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
    (_hEll : ell ≠ D.p) (s : SmoothDatum D) (G : Functors ell D s)
    (_rationalization : Rationalization G) (_integral : IntegralNormalization G) :
    Nonempty (Result G) := by
  sorry

end AlgebraicGeometry.ProEtale.NativeRationalFieldTransport
