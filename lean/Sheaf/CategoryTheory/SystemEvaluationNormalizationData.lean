/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.CategoryTheory.SystemRingedSequenceSite
public import Sheaf.CategoryTheory.SystemLevelLeftExtension
public import Sheaf.CategoryTheory.SystemSingleDerivedExtension
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.SystemSingletonGeometricPullback
public import Sheaf.CategoryTheory.DiagramRingRestrictionPushforward
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
public import Sheaf.CategoryTheory.SystemSingletonScalarExtension
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Mathlib.CategoryTheory.Adjunction.Mates
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
private theorem cachedRingCompose {T : Type*} [Category T]
    [EssentiallySmall.{w} T] (τ : GrothendieckTopology T) :
    τ.HasSheafCompose (CategoryTheory.forget RingCat.{w}) := inferInstance
private theorem cachedAddCompose {T : Type*} [Category T]
    [EssentiallySmall.{w} T] (τ : GrothendieckTopology T) :
    τ.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w}) := inferInstance
private theorem cachedCommCompose {T : Type*} [Category T]
    [EssentiallySmall.{w} T] (τ : GrothendieckTopology T) :
    τ.HasSheafCompose (CategoryTheory.forget CommRingCat.{w}) := inferInstance
attribute [local instance 20000] cachedRingCompose cachedAddCompose cachedCommCompose

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

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

/-- The geometric singleton isomorphism selected from its complete representative,
multiplication and lower-singleton normalization. Its representative equations determine
it uniquely, so this selects a specified comparison, not arbitrary isomorphic objects.
Source: Zheng 4.1 and the sentence before 4.10
(blueprint: lem-pur-system-evaluation-scalar-restriction-normalization). -/
def systemNormalizationSingleton
    (hF : SystemSingletonGeometricComparisons SY TY SX TX F) (n : ℕ) :
    (systemSingleDerivedExtension BY n SY TY).derived ⋙ F.functor.mapDerivedCategory ≅
      (F.levelFunctor n).mapDerivedCategory ⋙ (systemSingleDerivedExtension BX n SX TX).derived :=
  hF.choose_spec.choose_spec.choose n

attribute [local irreducible] systemNormalizationSingleton

variable (H : StrictRingSystem BX ⥤ StrictRingSystem BY) [H.Additive]
  [Abelian.HasKInjectiveResolutions (StrictRingSystem BX)]
  (adj : F.functor ⊣ H)
  (Hn : ∀ n : ℕ, systemLevel BX n ⥤ systemLevel BY n)
  [∀ n : ℕ, (Hn n).Additive]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (systemLevel BX n)]
  (adjn : ∀ n : ℕ, F.levelFunctor n ⊣ Hn n)

/-- The singleton Hom construction: conjugate c_n inverse under the two composite
adjunctions. Source: Zheng 4.1; Stacks 07A6; Mathlib's conjugateIsoEquiv
(blueprint: lem-pur-system-evaluation-scalar-restriction-normalization). -/
def systemNormalizationEvaluation
    (hF : SystemSingletonGeometricComparisons SY TY SX TX F) (n : ℕ) :
    H.rightDerivedFunctor ⋙ derivedSystemEvaluation BY n ≅
      derivedSystemEvaluation BX n ⋙ (Hn n).rightDerivedFunctor :=
  conjugateIsoEquiv
    ((systemSingleDerivedExtension BY n SY TY).adjunction.comp
      adj.mapDerivedCategoryRightDerivedAdjunction)
    ((adjn n).mapDerivedCategoryRightDerivedAdjunction.comp
      (systemSingleDerivedExtension BX n SX TX).adjunction)
    (systemNormalizationSingleton SY TY SX TX F hF n).symm

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
