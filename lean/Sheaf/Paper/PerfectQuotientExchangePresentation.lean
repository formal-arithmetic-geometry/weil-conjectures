/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.Paper.CompletedPullbackAdjunction
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Sheaf.Paper.StrictQuotientDiagonalNormalization
public import Sheaf.Paper.CompletionMateComparison
public import Sheaf.CategoryTheory.SystemEvaluationTopos
public import Sheaf.Paper.AugmentedDiagramProjectionMate
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison

/-! # Quotient-diagram exchange presentation

Source: Stacks Project, sites-cohomology.tex, Tags 0944, 0B56, 07A6 and 0D6E;
strict coefficient-exchange auxiliary, including the completion-unit calculation
(blueprint: def-pur-perfect-quotient-exchange-presentation).

The categories and scalar extensions are the published strict quotient sequence-site
constructions. Presentation data fix ordinary maps on all coefficient levels and fix
derived comparisons on entire cochain representatives, before evaluation or inverse limit.
Natural number n denotes the positive exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.proofsInPublic true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion

namespace CategoryTheory.AdicSites.PerfectQuotientExchange

variable (T : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A)

/-- The actual quotient-ring diagram module category, with semilinear transitions.
Source: Stacks 0940, 03CZ
(blueprint: def-pur-perfect-quotient-exchange-presentation). -/
abbrev Modules := Mod (strictQuotientRing T.topology A I)

/-- Standard localization for the actual quotient-ring diagram modules.
Source: Stacks 05RU (blueprint: def-pur-perfect-quotient-exchange-presentation). -/
instance quotientHasDerived : HasDerivedCategory (Modules T A I) :=
  HasDerivedCategory.standard _

/-- K-injective resolutions in the actual quotient-diagram module category.
This is the existing small-ringed-site Grothendieck construction.
Source: Stacks 079P, 0940
(blueprint: def-pur-perfect-quotient-exchange-presentation). -/
instance quotientKInjectives : Abelian.HasKInjectiveResolutions (Modules T A I) :=
  letI : IsGrothendieckAbelian.{u} (Modules T A I) :=
    SheafOfModules.isGrothendieckAbelian
      (siteModuleRings (strictQuotientRing T.topology A I))
  inferInstance

/-- Its ordinary unbounded derived category, localized before evaluation.
Source: Stacks 05RU, 0940
(blueprint: def-pur-perfect-quotient-exchange-presentation). -/
abbrev Derived := D (strictQuotientRing T.topology A I)

/-- Exact quotient-linear evaluation at positive level n+1.
Source: Stacks 0940, 03CZ
(blueprint: def-pur-perfect-quotient-exchange-presentation). -/
abbrev evaluation (n : ℕ) : Modules T A I ⥤ T.modules (quotientRing A I n) :=
  SheafOfModules.systemSequenceEvaluation (finiteSystem T.topology A I) n

/-- Additivity of the published exact quotient evaluation, with its actual section maps.
Source: Stacks 0940 (blueprint: def-pur-perfect-quotient-exchange-presentation). -/
instance evaluationAdditive (n : ℕ) : (evaluation T A I n).Additive :=
  SheafOfModules.systemSequenceEvaluationAdditive (finiteSystem T.topology A I) n

/-- Finite-limit preservation of the published quotient evaluation.
Source: Stacks 0940 (blueprint: def-pur-perfect-quotient-exchange-presentation). -/
instance evaluationLimits (n : ℕ) : PreservesFiniteLimits (evaluation T A I n) :=
  SheafOfModules.systemSequenceEvaluationLimits (finiteSystem T.topology A I) n

/-- Finite-colimit preservation of the published quotient evaluation.
Source: Stacks 0940 (blueprint: def-pur-perfect-quotient-exchange-presentation). -/
instance evaluationColimits (n : ℕ) : PreservesFiniteColimits (evaluation T A I n) :=
  SheafOfModules.systemSequenceEvaluationColimits (finiteSystem T.topology A I) n

/-- Evaluation on ordinary derived categories, retaining the quotient coefficients.
Source: Stacks 0940, 05RU
(blueprint: def-pur-perfect-quotient-exchange-presentation). -/
abbrev evaluationD (n : ℕ) : Derived T A I ⥤ T.derived (quotientRing A I n) :=
  (evaluation T A I n).mapDerivedCategory

variable {T A I}

/-- Quotient scalar extension of the exact diagonal, before localization.
Source: Stacks 06YY, 0940
(blueprint: def-pur-perfect-quotient-exchange-presentation). -/
abbrev reduction0 (d : StrictQuotientDiagonalPresentation T.topology A I) :=
  d.diagonal ⋙ change d.ringMap

/-- The canonical full-diagram reduction counit on a cochain representative.
Source: Stacks 06YY, 0940
(blueprint: def-pur-perfect-quotient-exchange-presentation). -/
def reductionComparison (d : StrictQuotientDiagonalPresentation T.topology A I)
    (P : CochainComplex (T.modules A) ℤ) :
    d.reductionD.obj ((Q (T.ring A)).obj P) ⟶
      (Q (strictQuotientRing T.topology A I)).obj
        (((reduction0 d).mapHomologicalComplex (.up ℤ)).obj P) :=
  d.reductionDIso.hom.app ((Q (T.ring A)).obj P) ≫
  (extend d.ringMap).map (d.diagonal.mapDerivedCategoryFactors.hom.app P) ≫
    (extendComparison d.ringMap).app ((d.diagonal.mapHomologicalComplex (.up ℤ)).obj P)

/-- The exact scalar-restriction comparison on a whole cochain representative.
Source: Stacks 03CZ, 05RU
(blueprint: def-pur-perfect-quotient-exchange-presentation). -/
def restrictionComparison (d : StrictQuotientDiagonalPresentation T.topology A I)
    (P : CochainComplex (Modules T A I) ℤ) :
    d.restrictionD.obj ((Q (strictQuotientRing T.topology A I)).obj P) ⟶
      (TQ (T.ring A)).obj ((d.restriction.mapHomologicalComplex (.up ℤ)).obj P) :=
  d.restrictionDIso.hom.app ((Q (strictQuotientRing T.topology A I)).obj P) ≫
  d.towers.functor.mapDerivedCategory.map
      ((res d.ringMap).mapDerivedCategoryFactors.hom.app P) ≫
    d.towers.functor.mapDerivedCategoryFactors.hom.app
      (((res d.ringMap).mapHomologicalComplex (.up ℤ)).obj P)

/-- Normalized evaluation and strict-tower comparisons for the published quotient reduction.
The first map is fixed on local pure tensors; the second is its entire K-flat cochain
square. The tower comparison is fixed by the published strict representative map.
Thus none of these comparisons is specified merely by its derived evaluations.
Source: Stacks 06YY, 0940, 0941
(blueprint: def-pur-perfect-quotient-exchange-presentation). -/
structure ReductionPresentation (d : StrictQuotientDiagonalPresentation T.topology A I) where
  ordinary : ∀ n : ℕ, reduction0 d ⋙ evaluation T A I n ≅
    change (quotient T.topology A I n)
  finite : ∀ n : ℕ, d.reductionD ⋙ evaluationD T A I n ≅ T.finiteReduction A I n
  tower : d.reductionD ⋙ d.restrictionD ≅ T.reduction A I
  forget : ∀ n : ℕ, d.restriction ⋙ (CategoryTheory.evaluation ℕᵒᵖ (T.modules A)).obj
    (op n) ≅ evaluation T A I n ⋙ res (quotient T.topology A I n)

/-- The ordinary section equations and full-cochain normalizations for this realization.
Source: Stacks 03CZ, 06YY, 07A6, 0940 and 0D6E
(blueprint: def-pur-perfect-quotient-exchange-presentation). -/
def ReductionNormalized (d : StrictQuotientDiagonalPresentation T.topology A I)
    (p : ReductionPresentation d) : Prop :=
  (∀ (n : ℕ) (M : T.modules A) (U : T.objectsᵒᵖ)
    (s : (ConstantCompletion.finite T.topology A I n).obj.obj U)
    (x : (d.diagonal.obj M).val.obj (op (n, U.unop))) (m : M.val.obj U)
    (z : ((evaluation T A I n).obj ((reduction0 d).obj M)).val.obj U),
    HEq x m → HEq z (tensorSection d.ringMap (d.diagonal.obj M) (op (n, U.unop)) s x) →
      ((p.ordinary n).hom.app M).val.app U z =
        tensorSection (quotient T.topology A I n) M U s m) ∧
  (∀ (n : ℕ) (P : CochainComplex (T.modules A) ℤ),
    P.IsAcyclicTensorKFlat → (∀ q : ℤ, (P.X q).IsFlat) →
    (evaluationD T A I n).map (reductionComparison d P) ≫
        (evaluation T A I n).mapDerivedCategoryFactors.hom.app
          (((reduction0 d).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (Q (T.ring (quotientRing A I n))).map
          ((mapComplexSquare (reduction0 d) (evaluation T A I n)
            (𝟭 (T.modules A)) (change (quotient T.topology A I n))
            (p.ordinary n)).hom.app P) =
      (p.finite n).hom.app ((Q (T.ring A)).obj P) ≫
        (extendComparison (quotient T.topology A I n)).app P) ∧
  (∀ P : CochainComplex (T.modules A) ℤ,
    P.IsAcyclicTensorKFlat → (∀ q : ℤ, (P.X q).IsFlat) →
    p.tower.hom.app ((Q (T.ring A)).obj P) ≫
        (quotientPresentation T.topology A I false).comparison.app P = d.representative P) ∧
  (∀ (n : ℕ) (M : Modules T A I) (U : T.objectsᵒᵖ)
    (x : ((d.restriction.obj M).obj (op n)).val.obj U),
    HEq (((p.forget n).hom.app M).val.app U x) x)

variable {Y X : Site.{u}} (f : Morphism Y X) (A : Type u) [CommRing A] (I : Ideal A)

/-- The canonical module adjunction on the quotient diagram, with levelwise Hom
normalization and full-cochain derived comparison normalizations. Existence is a
conclusion of the main theorem. All module categories, evaluations, reductions, tensor
counits and the ambient derived adjunction come from the recorded dependency APIs.
Source: Stacks 03D7, 07A6, 0D6E, 06YY and 0940
(blueprint: def-pur-perfect-quotient-exchange-presentation). -/
structure Presentation where
  atY : StrictQuotientDiagonalPresentation Y.topology A I
  atX : StrictQuotientDiagonalPresentation X.topology A I
  reductionY : ReductionPresentation atY
  reductionX : ReductionPresentation atX
  pull : Modules Y A I ⥤ Modules X A I
  push : Modules X A I ⥤ Modules Y A I
  [pull_additive : pull.Additive]
  [push_additive : push.Additive]
  [pull_limits : PreservesFiniteLimits pull]
  [pull_colimits : PreservesFiniteColimits pull]
  adjunction : pull ⊣ push
  pullEvaluation : ∀ n : ℕ, pull ⋙ evaluation X A I n ≅
    evaluation Y A I n ⋙ f.modulePull (quotientRing A I n)
  pushEvaluation : ∀ n : ℕ, push ⋙ evaluation Y A I n ≅
    evaluation X A I n ⋙ f.modulePush (quotientRing A I n)
  restriction0 : atY.restriction ⋙ f.towerModulePull A ≅ pull ⋙ atX.restriction
  reduction0 : PerfectQuotientExchange.reduction0 atY ⋙ pull ≅
    f.modulePull A ⋙ PerfectQuotientExchange.reduction0 atX
  restriction : atY.restrictionD ⋙ f.towerPull A ≅ pull.mapDerivedCategory ⋙ atX.restrictionD
  reduction : atY.reductionD ⋙ pull.mapDerivedCategory ≅ f.pull A ⋙ atX.reductionD
  pushEvaluationD : ∀ n : ℕ, push.rightDerivedFunctor ⋙ evaluationD Y A I n ≅
    evaluationD X A I n ⋙ f.push (quotientRing A I n)

attribute [instance] Presentation.pull_additive Presentation.push_additive
  Presentation.pull_limits Presentation.pull_colimits


/-- The ordinary section equations and full-cochain normalizations for this realization.
Source: Stacks 03CZ, 06YY, 07A6, 0940 and 0D6E
(blueprint: def-pur-perfect-quotient-exchange-presentation). -/
def PresentationNormalized (p : Presentation f A I) : Prop :=
  ReductionNormalized p.atY p.reductionY ∧ ReductionNormalized p.atX p.reductionX ∧
  (∀ (M : Modules Y A I) (N : Modules X A I)
    (g : p.pull.obj M ⟶ N) (n : ℕ),
    (evaluation Y A I n).map (p.adjunction.homEquiv M N g) ≫
        (p.pushEvaluation n).hom.app N =
      (f.moduleAdjunction (quotientRing A I n)).homEquiv _ _
        ((p.pullEvaluation n).inv.app M ≫ (evaluation X A I n).map g)) ∧
  (∀ (M : Modules Y A I) (n : ℕ),
    ((CategoryTheory.evaluation ℕᵒᵖ (X.modules A)).obj (op n)).map
        (p.restriction0.hom.app M) ≫ (p.reductionX.forget n).hom.app (p.pull.obj M) =
      (f.modulePull A).map ((p.reductionY.forget n).hom.app M) ≫
        (f.finiteModuleRestrictionPullIso A I n).hom.app ((evaluation Y A I n).obj M) ≫
          (res (quotient X.topology A I n)).map ((p.pullEvaluation n).inv.app M)) ∧
  (∀ (M : Y.modules A) (n : ℕ),
    (evaluation X A I n).map (p.reduction0.hom.app M) ≫
        (p.reductionX.ordinary n).hom.app ((f.modulePull A).obj M) =
      (p.pullEvaluation n).hom.app ((PerfectQuotientExchange.reduction0 p.atY).obj M) ≫
        (f.modulePull (quotientRing A I n)).map ((p.reductionY.ordinary n).hom.app M) ≫
          (ordinaryFinitePull f.algebra f.direct f.adjunction A I n).inv.app M) ∧
  (∀ P : CochainComplex (Modules Y A I) ℤ,
    (f.towerPull A).map (restrictionComparison p.atY P) ≫
        (f.towerModulePull A).mapDerivedCategoryFactors.hom.app
          ((p.atY.restriction.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (TQ (X.ring A)).map
          ((mapComplexSquare p.atY.restriction (f.towerModulePull A) p.pull p.atX.restriction
            p.restriction0).hom.app P) =
      p.restriction.hom.app ((Q (strictQuotientRing Y.topology A I)).obj P) ≫
        p.atX.restrictionD.map (p.pull.mapDerivedCategoryFactors.hom.app P) ≫
          restrictionComparison p.atX ((p.pull.mapHomologicalComplex (.up ℤ)).obj P)) ∧
  (∀ P : CochainComplex (Y.modules A) ℤ,
    P.IsAcyclicTensorKFlat → (∀ q : ℤ, (P.X q).IsFlat) →
    p.pull.mapDerivedCategory.map (reductionComparison p.atY P) ≫
        p.pull.mapDerivedCategoryFactors.hom.app
          (((PerfectQuotientExchange.reduction0 p.atY).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (Q (strictQuotientRing X.topology A I)).map
          ((mapComplexSquare (PerfectQuotientExchange.reduction0 p.atY) p.pull
            (f.modulePull A) (PerfectQuotientExchange.reduction0 p.atX) p.reduction0).hom.app P) =
      p.reduction.hom.app ((Q (Y.ring A)).obj P) ≫
        p.atX.reductionD.map ((f.modulePull A).mapDerivedCategoryFactors.hom.app P) ≫
          reductionComparison p.atX (((f.modulePull A).mapHomologicalComplex (.up ℤ)).obj P)) ∧
  (∀ (n : ℕ) (P : CochainComplex (Modules X A I) ℤ),
    (evaluationD Y A I n).map
        (p.push.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (p.pushEvaluationD n).hom.app ((Q (strictQuotientRing X.topology A I)).obj P) ≫
        (f.push (quotientRing A I n)).map
          ((evaluation X A I n).mapDerivedCategoryFactors.hom.app P) =
      (evaluation Y A I n).mapDerivedCategoryFactors.hom.app
        ((p.push.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (Q (Y.ring (quotientRing A I n))).map
          ((mapComplexSquare p.push (evaluation Y A I n) (evaluation X A I n)
            (f.modulePush (quotientRing A I n)) (p.pushEvaluation n)).hom.app P) ≫
        f.pushUnit (quotientRing A I n)
          (((evaluation X A I n).mapHomologicalComplex (.up ℤ)).obj P))

variable {f A I} (p : Presentation f A I)

/-- The quotient-diagram derived adjunction induced from the normalized module adjunction.
Source: Stacks 07A6 (blueprint: def-pur-perfect-quotient-exchange-presentation). -/
def Presentation.derivedAdjunction : p.pull.mapDerivedCategory ⊣ p.push.rightDerivedFunctor :=
  p.adjunction.mapDerivedCategoryRightDerivedAdjunction

/-- The coefficient-exchange mate of scalar extension of the ambient counit.
The input square is normalized on full flat-term K-flat representatives.
Source: Stacks 0B56, 07A6
(blueprint: def-pur-perfect-quotient-exchange-presentation). -/
def exchange : f.push A ⋙ p.atY.reductionD ⟶ p.atX.reductionD ⋙ p.push.rightDerivedFunctor :=
  (mateEquiv (f.adj A) p.derivedAdjunction
    (TwoSquare.mk _ _ _ _ p.reduction.hom)).natTrans

/-- The scalar-restriction mate; the theorem identifies it with the invertible
canonical derived-composition comparison d, before evaluation or inverse limit.
Source: Stacks 0D6E, 07A6
(blueprint: def-pur-perfect-quotient-exchange-presentation). -/
def restrictionMate : p.push.rightDerivedFunctor ⋙ p.atY.restrictionD ⟶
    p.atX.restrictionD ⋙ f.towerPush A :=
  (mateEquiv p.derivedAdjunction (f.towerAdjunction A)
    (TwoSquare.mk _ _ _ _ p.restriction.hom)).natTrans

/-- The strict projection mate, with the source and target expressed in the
published quotient-diagram reduction. This is the equivalent counit-transpose
construction of augmentedDiagramProjectionMate; it uses the specified chi implicitly
through the normalized reduction/pullback comparison, not a new Hom bijection.
Source: Stacks 0B56 and the strict augmented-diagram auxiliary
(blueprint: def-pur-perfect-quotient-exchange-presentation). -/
def strictExchange : f.push A ⋙ p.atY.reductionD ⋙ p.atY.restrictionD ⟶
    p.atX.reductionD ⋙ p.atX.restrictionD ⋙ f.towerPush A :=
  Functor.whiskerLeft (f.push A) p.reductionY.tower.hom ≫
    (mateEquiv (f.adj A) (f.towerAdjunction A)
      (TwoSquare.mk _ _ _ _ (f.reductionPullIso A I).hom)).natTrans ≫
        Functor.whiskerRight p.reductionX.tower.inv (f.towerPush A)

/-- Quotient-linear evaluation of h, with the specified evaluation/direct-image and
reduction comparisons inserted at its endpoints. It is a natural transformation,
not a family of separately selected quotient-linear maps.
Source: Stacks 0B56, 07A6, 0940
(blueprint: def-pur-perfect-quotient-exchange-presentation). -/
def finiteExchange (n : ℕ) : f.push A ⋙ Y.finiteReduction A I n ⟶
    X.finiteReduction A I n ⋙ f.push (quotientRing A I n) :=
  Functor.whiskerLeft (f.push A) (p.reductionY.finite n).inv ≫
    Functor.whiskerRight (exchange p) (evaluationD Y A I n) ≫
      Functor.whiskerLeft p.atX.reductionD (p.pushEvaluationD n).hom ≫
        Functor.whiskerRight (p.reductionX.finite n).hom (f.push (quotientRing A I n))

/-- Rho is Rlim(h^A) followed by the inverse direct-image/limit comparison.
The endpoint isomorphisms express L U R = C via the representative-normalized
strict quotient comparison. The completion functor and its unit are the fixed reflector.
Source: Stacks 0941, 0A07 and the strict quotient auxiliary
(blueprint: def-pur-perfect-quotient-exchange-presentation). -/
def completionExchange (F : X.derived A) :
    (Y.completion A I).obj ((f.push A).obj F) ⟶
      (f.push A).obj ((X.completion A I).obj F) :=
  (Y.rlim A).map (p.reductionY.tower.inv.app ((f.push A).obj F)) ≫
    (Y.rlim A).map ((strictExchange p).app F) ≫
      (f.directLimitIso A).inv.app
        (p.atX.restrictionD.obj (p.atX.reductionD.obj F)) ≫
        (f.push A).map ((X.rlim A).map (p.reductionX.tower.hom.app F))

end CategoryTheory.AdicSites.PerfectQuotientExchange
