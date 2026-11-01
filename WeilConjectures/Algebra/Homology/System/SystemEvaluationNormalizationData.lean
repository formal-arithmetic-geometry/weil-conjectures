/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtension
public import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedExtension
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.Algebra.Homology.System.SystemSingletonGeometricPullback
public import WeilConjectures.CategoryTheory.Diagram.DiagramRingRestrictionPushforward
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.CategoryTheory.SmoothBaseChange.TowerDerivedEvaluationNormalization
public import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarExtension
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Diagram.DiagramSiteModuleEquivalence
public import WeilConjectures.CategoryTheory.Diagram.DiagramSiteTopology
public import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
/-! # Scalar normalization of singleton evaluation and direct image

Source: Stacks, Tags 0D6D, 07A6 and 0D6E; Zheng, Construction 4.1 and the comparison
before Lemma 4.10. The scalar square is the agent mate-pasting auxiliary
(blueprint: lem-pur-system-evaluation-scalar-restriction-normalization).

All derived categories are ordinary unbounded localizations. Positive level n+1 is
encoded by n : ℕ. Ordinary adjunctions are retained before deriving; no varying-ring
evaluation is assumed to preserve K-injectives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance 20000] comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

private theorem cachedCommCompose {T : Type*} [Category T]
    [EssentiallySmall.{w} T] (τ : GrothendieckTopology T) :
    τ.HasSheafCompose (CategoryTheory.forget CommRingCat.{w}) := inferInstance

/-- Actual restriction of strict systems, transported from the recorded sequence-site
restriction. Source: Stacks 03DA; Zheng 4.1
(blueprint: lem-pur-system-evaluation-scalar-restriction-normalization). -/
def systemNormalizationRestriction {A B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) : StrictRingSystem B ⥤ StrictRingSystem A :=
  (strictSystemSequenceEquivalence B).functor ⋙ singletonSequenceRestriction a ⋙
    (strictSystemSequenceEquivalence A).inverse

/-- The existing exact sequence-site restriction structure, transported across equivalences.
Source: Stacks 03DA (blueprint: lem-pur-system-evaluation-scalar-restriction-normalization). -/
instance systemNormalizationRestrictionAdditive {A B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) : (systemNormalizationRestriction a).Additive :=
  inferInstanceAs ((
    (strictSystemSequenceEquivalence B).functor ⋙ singletonSequenceRestriction a ⋙
      (strictSystemSequenceEquivalence A).inverse).Additive)

/-- The existing exact sequence-site restriction structure, transported across equivalences.
Source: Stacks 03DA (blueprint: lem-pur-system-evaluation-scalar-restriction-normalization). -/
instance systemNormalizationRestrictionLimits {A B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) : PreservesFiniteLimits (systemNormalizationRestriction a) :=
  inferInstanceAs (PreservesFiniteLimits (
    (strictSystemSequenceEquivalence B).functor ⋙ singletonSequenceRestriction a ⋙
      (strictSystemSequenceEquivalence A).inverse))

/-- The existing exact sequence-site restriction structure, transported across equivalences.
Source: Stacks 03DA (blueprint: lem-pur-system-evaluation-scalar-restriction-normalization). -/
instance systemNormalizationRestrictionColimits {A B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) : PreservesFiniteColimits (systemNormalizationRestriction a) :=
  inferInstanceAs (PreservesFiniteColimits (
    (strictSystemSequenceEquivalence B).functor ⋙ singletonSequenceRestriction a ⋙
      (strictSystemSequenceEquivalence A).inverse))

/-- Restriction/evaluation is the identity on sections, with the sequence equivalence's
unit made explicit. Source: Stacks 03DA; Zheng 4.1
(blueprint: lem-pur-system-evaluation-scalar-restriction-normalization). -/
def systemNormalizationRestrictionEvaluation {A B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) (n : ℕ) :
    systemNormalizationRestriction a ⋙ systemEvaluation A n ≅
      systemEvaluation B n ⋙ singletonLevelRestriction a n :=
  Functor.isoWhiskerLeft (strictSystemSequenceEquivalence B).functor
      (singletonRestrictionEvaluation a n) ≪≫
    Functor.isoWhiskerRight (strictSystemSequenceEquivalence B).unitIso.symm
      (systemEvaluation B n ⋙ singletonLevelRestriction a n)

/-- Localization of the actual restriction/evaluation identification.
Source: Stacks 015F (blueprint: lem-pur-system-evaluation-scalar-restriction-normalization). -/
def systemNormalizationDerivedRestrictionEvaluation
    {A B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : A ⟶ B) (n : ℕ) :
    (systemNormalizationRestriction a).mapDerivedCategory ⋙ derivedSystemEvaluation A n ≅
      derivedSystemEvaluation B n ⋙ (singletonLevelRestriction a n).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso (systemNormalizationRestrictionEvaluation a n)

attribute [local irreducible] systemNormalizationRestriction
  systemNormalizationRestrictionEvaluation systemNormalizationDerivedRestrictionEvaluation

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [EssentiallySmall.{w} D]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  {BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w}}
  {uTop : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))}
  {I : ∀ n : ℕ, AlgebraicInverseImage uTop.inverse (BY.obj (op n)) (BX.obj (op n))}
  (SY : SystemScalarAssignment (J := J)) (TY : SystemTensorCoherence SY)
  (SX : SystemScalarAssignment (J := K)) (TX : SystemTensorCoherence SX)
  (F : SystemGeometricInverseImageData BY BX uTop I)

attribute [local irreducible] systemNormalizationSingleton

variable (H : StrictRingSystem BX ⥤ StrictRingSystem BY) [H.Additive]
  [Abelian.HasKInjectiveResolutions (StrictRingSystem BX)]
  (adj : F.functor ⊣ H)
  (Hn : ∀ n : ℕ, systemLevel BX n ⥤ systemLevel BY n)
  [∀ n : ℕ, (Hn n).Additive]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (systemLevel BX n)]
  (adjn : ∀ n : ℕ, F.levelFunctor n ⊣ Hn n)

end SheafOfModules

namespace CategoryTheory.SystemEvaluationNormalization

universe a b c d va vb vc vd qA qB qA' qB'
variable {A : Type a} {B : Type b} {A' : Type c} {B' : Type d}
  [Category.{va} A] [Category.{vb} B] [Category.{vc} A'] [Category.{vd} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{qA} A] [HasDerivedCategory.{qB} B]
  [HasDerivedCategory.{qA'} A'] [HasDerivedCategory.{qB'} B']
  [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions B']
  {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  {U : A ⥤ A'} {V : B ⥤ B'} [U.Additive] [V.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]

/-- Ordinary right mate of the canonical restriction/pullback square.
Source: Stacks 07A6 (blueprint: lem-pur-system-evaluation-scalar-restriction-normalization). -/
def ordinaryMate (adj : L ⊣ R) (adj' : L' ⊣ R') (s : L ⋙ V ≅ U ⋙ L') :
    R ⋙ U ⟶ V ⋙ R' :=
  (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.inv)).natTrans

/-- Derived right mate, using the module-induced derived adjunctions and the exact
localization of the ordinary square. Source: Stacks 0D6E and 07A6
(blueprint: lem-pur-system-evaluation-scalar-restriction-normalization). -/
def derivedMate (adj : L ⊣ R) (adj' : L' ⊣ R') (s : L ⋙ V ≅ U ⋙ L') :
    R.rightDerivedFunctor ⋙ U.mapDerivedCategory ⟶
      V.mapDerivedCategory ⋙ R'.rightDerivedFunctor :=
  (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
    adj'.mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso s).inv)).natTrans

/-- The resolution-unit equation for the two factorizations of the same ringed morphism.
This is the normalization of diagramRingRestrictionPushforward, written on the homotopy
presentation of the same unbounded localization. Source: Stacks 0D6E
(blueprint: lem-pur-system-evaluation-scalar-restriction-normalization). -/
def UnitNormalized (adj : L ⊣ R) (adj' : L' ⊣ R') (s : L ⋙ V ≅ U ⋙ L') : Prop :=
  ∀ M : HomotopyCategory B (.up ℤ),
    U.mapDerivedCategoryFactorsh.inv.app ((R.mapHomotopyCategory (.up ℤ)).obj M) ≫
        U.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app M) ≫
        (derivedMate adj adj' s).app (DerivedCategory.Qh.obj M) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (ordinaryMate adj adj' s) (.up ℤ)).app M) ≫
        R'.rightDerivedFunctorUnit.app ((V.mapHomotopyCategory (.up ℤ)).obj M) ≫
        R'.rightDerivedFunctor.map (V.mapDerivedCategoryFactorsh.inv.app M)

end CategoryTheory.SystemEvaluationNormalization

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [EssentiallySmall.{w} D]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  (AY : Sheaf J CommRingCat.{w}) (AX : Sheaf K CommRingCat.{w})
  (BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w})
  (aY : (Functor.const ℕᵒᵖ).obj AY ⟶ BY)
  (aX : (Functor.const ℕᵒᵖ).obj AX ⟶ BX)
  (uTop : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
  (IA : AlgebraicInverseImage uTop.inverse AY AX)
  (IB : ∀ n : ℕ, AlgebraicInverseImage uTop.inverse (BY.obj (op n)) (BX.obj (op n)))
  (FB : SystemGeometricInverseImageData BY BX uTop IB)
  (FA : SystemGeometricInverseImageData
    ((Functor.const ℕᵒᵖ).obj AY) ((Functor.const ℕᵒᵖ).obj AX) uTop (fun _ ↦ IA))

/-- The ordinary commuting squares, pinned by the identity on underlying inverse-image
sheaves. These are conclusions of the theorem below. The last square uses actual level
restriction, so its mate is the coefficient/direct-image comparison for transitions.
Source: Stacks 03D2 and 0D6E; Zheng 4.1
(blueprint: lem-pur-system-evaluation-scalar-restriction-normalization). -/
structure SystemNormalizationSquares where
  level : ∀ n : ℕ,
    FB.levelFunctor n ⋙ singletonLevelRestriction aX n ≅
      singletonLevelRestriction aY n ⋙ FA.levelFunctor 0
  levelUnderlying : ∀ (n : ℕ) (M : systemLevel BY n),
    (systemGeometricUnderlying ((Functor.const ℕᵒᵖ).obj AX) 0).map
          ((level n).hom.app M) ≫
        IA.moduleUnderlying.hom.app ((singletonLevelRestriction aY n).obj M) =
      (IB n).moduleUnderlying.hom.app M
  scalar : FB.functor ⋙ systemNormalizationRestriction aX ≅
    systemNormalizationRestriction aY ⋙ FA.functor
  scalarEvaluation : ∀ (M : StrictRingSystem BY) (n : ℕ),
    (systemEvaluation ((Functor.const ℕᵒᵖ).obj AX) n).map (scalar.hom.app M) ≫
        (FA.evaluation n).hom.app ((systemNormalizationRestriction aY).obj M) ≫
        (FA.levelFunctor 0).map
          ((systemNormalizationRestrictionEvaluation aY n).hom.app M) =
      (systemNormalizationRestrictionEvaluation aX n).hom.app (FB.functor.obj M) ≫
        (singletonLevelRestriction aX n).map ((FB.evaluation n).hom.app M) ≫
        (level n).hom.app (M.level n)
  restriction : ∀ {n m : ℕ} (h : n ≤ m),
    FB.levelFunctor n ⋙ systemRestriction BX h ≅
      systemRestriction BY h ⋙ FB.levelFunctor m
  restrictionUnderlying : ∀ {n m : ℕ} (h : n ≤ m) (M : systemLevel BY n),
    (systemGeometricUnderlying BX m).map ((restriction h).hom.app M) ≫
        (IB m).moduleUnderlying.hom.app ((systemRestriction BY h).obj M) =
      (IB n).moduleUnderlying.hom.app M

end SheafOfModules
