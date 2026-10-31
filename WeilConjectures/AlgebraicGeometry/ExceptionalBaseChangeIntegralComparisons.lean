/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerMateEvaluationReduction
public import WeilConjectures.AlgebraicGeometry.IntegralAdjunctionBijection
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantExact
public import WeilConjectures.AlgebraicGeometry.SmoothExceptionalBaseChangeStatement
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGamma
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Exceptional base change for strict towers and integral coefficients

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-purity-bc,
sk-prop-sp-purity-bc-tower.md, clauses (1)--(3)
(blueprint: def-sp-exceptional-bc-integral-comparisons).

Every natural-number level n denotes the positive exponent n+1. Tower maps are
morphisms in the ordinary localization of the strict varying-coefficient category.
Integral objects use the completed coefficient sheaf, rather than its discrete model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures Opposite

namespace AlgebraicGeometry.ProEtale.SpExceptionalBaseChange

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- Reduction and its total-limit reconstruction on the integral constructible category.
Source: clause (3), normalized-equivalence and its unit
(blueprint: def-sp-exceptional-bc-integral-comparisons). -/
structure IntegralCoordinates (T : Scheme.{u}) where
  reduction : SpReductionTower l E T (q.abelian T)
  normalization : SpNormalizedEquivalence l E T (q.abelian T) reduction
  closed : ∀ K : sfIntegralConstructibleCategory l E T,
    spConstructibleTorTowers l E T (q.abelian T)
      ((SpIntegralAdjunction.reduction l E T (q.abelian T) reduction).obj K)
  normalized : ∀ K : sfIntegralConstructibleCategory l E T,
    IsSpNormalizedTower l E T (q.abelian T)
      ((SpIntegralAdjunction.reduction l E T (q.abelian T) reduction).obj K)
  fullyFaithful :
    (SpIntegralAdjunction.reduce l E T (q.abelian T) reduction closed).FullyFaithful
  cofinal : SpTwistedPullback.CofinalModel l E b T
  strict : IntegralStrictReductionModel l E T
  cofinalReduction : SpTwistedPullback.CofinalReduction l E b T
    (q.abelian T) reduction strict cofinal
  unit : ∀ K : sfIntegralConstructibleCategory l E T,
    IsIso (normalization.adjunction.unit.app K.obj)

/-- The published reduction, restricted using its constructibility certificate.
Source: clause (3), red_T (blueprint: def-sp-exceptional-bc-integral-comparisons). -/
abbrev red {T : Scheme.{u}} (r : IntegralCoordinates l E b q T) :=
  SpIntegralAdjunction.reduce l E T (q.abelian T) r.reduction r.closed

/-- The published total derived inverse limit, after restriction of scalar actions.
Source: clause (3), R lim (blueprint: def-sp-exceptional-bc-integral-comparisons). -/
abbrev lim {T : Scheme.{u}} (r : IntegralCoordinates l E b q T) :=
  SpIntegralAdjunction.limit l E T (q.abelian T) r.reduction r.normalization

/-- The cofinal inverse-image comparison, fixed as the mate of the identity
on direct-image sections, before deriving either strict functor.
Source: clause (3), completed-pullback comparison
(blueprint: def-sp-exceptional-bc-integral-comparisons). -/
structure PullModel {U T : Scheme.{u}} (h : U ⟶ T)
    (rU : IntegralCoordinates l E b q U) (rT : IntegralCoordinates l E b q T) where
  direct : pullbackTensorSequenceDirect l E h ⋙ rT.cofinal.ordinary ≅
    rU.cofinal.ordinary ⋙ (o.geometry h).push
  sections : ∀ (M : coefficientSequenceModules l E U) (n : ℕ) (V : T.ProEtᵒᵖ)
    (z : ((pullbackTensorSequenceDirect l E h ⋙ rT.cofinal.ordinary).obj M).val.obj
      (op (n, V.unop))),
    HEq ((direct.hom.app M).val.app (op (n, V.unop)) z) z
  inverseImage : rT.cofinal.ordinary ⋙ (o.geometry h).pull ≅
    pullbackTensorSequenceInverse l E h ⋙ rU.cofinal.ordinary
  mate : ∀ M : coefficientSequenceModules l E T,
    ((o.geometry h).ordinaryAdjunction.homEquiv _ _) (inverseImage.hom.app M) =
      rT.cofinal.ordinary.map ((pullbackTensorSequenceAdjunction l E h).unit.app M) ≫
        direct.hom.app ((pullbackTensorSequenceInverse l E h).obj M)

/-- Exact localization of the preceding ordinary mate, including both composition
comparisons. Source: clause (3) (blueprint: def-sp-exceptional-bc-integral-comparisons). -/
def PullModel.derived {U T : Scheme.{u}} {h : U ⟶ T}
    {rU : IntegralCoordinates l E b q U} {rT : IntegralCoordinates l E b q T}
    (m : PullModel l E b o q h rU rT) :=
  (Functor.mapDerivedCategoryCompIso rT.cofinal.ordinary (o.geometry h).pull).symm ≪≫
    Functor.mapDerivedCategoryNatIso m.inverseImage ≪≫
    Functor.mapDerivedCategoryCompIso (pullbackTensorSequenceInverse l E h) rU.cofinal.ordinary

/-- The whole-tower pullback comparison: the uniquely Roos-normalized integral
pullback model, the native reconstruction counit, and the section-normalized cofinal
comparison. No family of finite arrows is lifted by choice.
Source: clause (3), reconstruction counit
(blueprint: def-sp-exceptional-bc-integral-comparisons). -/
@[irreducible] def pullReduction {U T : Scheme.{u}} (h : U ⟶ T)
    (rU : IntegralCoordinates l E b q U) (rT : IntegralCoordinates l E b q T)
    (m : PullModel l E b o q h rU rT)
    (K : sfIntegralConstructibleCategory l E T) :=
  (SpTowerCalculus.realization l E b U (q.abelian U)).unitIso.hom.app
      ((spCompletedReduction l E U (q.abelian U) rU.reduction).obj
        ((integralDerivedPullback l E h).obj K.obj)) ≫
    (SpTowerCalculus.realization l E b U (q.abelian U)).inverse.map
      (rU.cofinalReduction.derived.inv.app ((integralDerivedPullback l E h).obj K.obj) ≫
        rU.cofinal.ordinary.mapDerivedCategory.map
          ((pullbackTensorCalculus l E U).reduction.map
              ((pullbackTensorIntegralPullbackModel l E h).hom.app K.obj) ≫
            (pullbackTensorCalculus l E U).adjunction.counit.app
              ((pullbackTensorSequenceDerived l E h).obj
                ((pullbackTensorCalculus l E T).reduction.obj K.obj))) ≫
        (PullModel.derived l E b o q m).inv.app
          ((pullbackTensorCalculus l E T).reduction.obj K.obj) ≫
        (SpTowerShriek.pull l E b (o.geometry h)).map
          (rT.cofinalReduction.derived.hom.app K.obj))

variable {X' X Y' Y : Scheme.{u}} {u' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {v : Y' ⟶ Y} {sq : IsPullback u' f' f v} {c : Compactification f}
  (a : SpTowerMate.Data l E b o q sq c)

/-- The dependency's complete reconstruction package for a compactification,
transporting only the equality f = j followed by p. Its scalar comparison is fixed
on ordinary quotient generators and on derived composition units.
Source: clause (3), integral-direct-image-tower and integral-adjunction-bijection
(blueprint: def-sp-exceptional-bc-integral-comparisons). -/
def SupportModel {U T : Scheme.{u}} {h : U ⟶ T} [QuasiCompact h]
    (c : Compactification h)
    (rU : IntegralCoordinates l E b q U) (rT : IntegralCoordinates l E b q T)
    (hF : ∀ M : SpTowerCalculus.C l E b q U,
      spConstructibleTorTowers l E T (q.abelian T)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q T ⥤ SpTowerCalculus.C l E b q U)
    (adj : SpTowerGluing.support l E b o q c hF ⊣ G) : Type _ :=
  letI : QuasiCompact (c.i ≫ c.g) := c.comm ▸ inferInstance
  letI : HasCompactification (c.i ≫ c.g) :=
    (SpTowerGamma.factorization c.i c.g).hasCompactification
  SpIntegralAdjunction.Reconstruction l E b o q c.i c.g
    rU.reduction rU.normalization rT.reduction rT.normalization hF G adj

/-- Extract the dependency's fixed reduction comparison with the compactification
instances retained. Source: clause (3) (blueprint: def-sp-exceptional-bc-integral-comparisons). -/
def supportComparisonModel {U T : Scheme.{u}} {h : U ⟶ T} [QuasiCompact h]
    (c : Compactification h)
    (rU : IntegralCoordinates l E b q U) (rT : IntegralCoordinates l E b q T)
    (hF : ∀ M : SpTowerCalculus.C l E b q U,
      spConstructibleTorTowers l E T (q.abelian T)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q T ⥤ SpTowerCalculus.C l E b q U)
    (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
    (r : SupportModel l E b o q c rU rT hF G adj) :=
  letI : QuasiCompact (c.i ≫ c.g) := c.comm ▸ inferInstance
  letI : HasCompactification (c.i ≫ c.g) :=
    (SpTowerGamma.factorization c.i c.g).hasCompactification
  r.leftComparison

/-- Integral operation comparisons, using the completed pullbacks and the separately
 derived compactification functors. The right adjoints are identified with H by the
 reconstruction counit; their counits reduce to the tower counits. These data are
 supplied in the conclusion, not imposed as geometric hypotheses.
Source: clause (3), comparison conventions and integral-adjunction-bijection
(blueprint: def-sp-exceptional-bc-integral-comparisons). -/
structure IntegralData
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ x : X', Invertible (l : X'.residueField x)]
    [∀ y : Y', Invertible (l : Y'.residueField y)] where
  [quasiCompact : QuasiCompact f]
  [quasiCompact' : QuasiCompact f']
  rX : IntegralCoordinates l E b q X
  rY : IntegralCoordinates l E b q Y
  rX' : IntegralCoordinates l E b q X'
  rY' : IntegralCoordinates l E b q Y'
  support_closed : ∀ M : sfIntegralConstructibleCategory l E X,
    sfIntegralConstructible l E Y ((CompleteCompactificationLimit.image l E c).obj M.obj)
  support_closed' : ∀ M : sfIntegralConstructibleCategory l E X',
    sfIntegralConstructible l E Y'
      ((CompleteCompactificationLimit.image l E (c.ofIsPullback sq)).obj M.obj)
  supportModel : SupportModel l E b o q c rX rY a.support_closed a.right a.adjunction
  supportModel' : SupportModel l E b o q (c.ofIsPullback sq) rX' rY'
    a.support_closed' a.right' a.adjunction'
  right : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X
  right' : sfIntegralConstructibleCategory l E Y' ⥤ sfIntegralConstructibleCategory l E X'
  adjunction : SpIntegralAdjunction.support l E c support_closed ⊣ right
  adjunction' : SpIntegralAdjunction.support l E (c.ofIsPullback sq) support_closed' ⊣ right'
  supportComparison : SpIntegralAdjunction.support l E c support_closed ⋙ red l E b q rY ≅
    red l E b q rX ⋙ SpTowerGluing.support l E b o q c a.support_closed
  supportComparison' :
    SpIntegralAdjunction.support l E (c.ofIsPullback sq) support_closed' ⋙ red l E b q rY' ≅
      red l E b q rX' ⋙
        SpTowerGluing.support l E b o q (c.ofIsPullback sq) a.support_closed'
  support_normalized : HEq supportComparison
    (supportComparisonModel l E b o q c rX rY a.support_closed a.right a.adjunction supportModel)
  support_normalized' : HEq supportComparison'
    (supportComparisonModel l E b o q (c.ofIsPullback sq) rX' rY'
      a.support_closed' a.right' a.adjunction' supportModel')
  exceptionalComparison : right ⋙ red l E b q rX ≅ red l E b q rY ⋙ a.right
  exceptionalComparison' : right' ⋙ red l E b q rX' ≅ red l E b q rY' ⋙ a.right'
  rightLimit : right ⋙ (sfIntegralConstructible l E X).ι ≅
    red l E b q rY ⋙ a.right ⋙ SpTowerCalculus.inclusion l E b q X ⋙ lim l E b q rX
  rightLimit' : right' ⋙ (sfIntegralConstructible l E X').ι ≅
    red l E b q rY' ⋙ a.right' ⋙ SpTowerCalculus.inclusion l E b q X' ⋙ lim l E b q rX'
  right_reduction : ∀ K : sfIntegralConstructibleCategory l E Y,
    (exceptionalComparison.hom.app K).hom =
      (spCompletedReduction l E X (q.abelian X) rX.reduction).map
          (rightLimit.hom.app K) ≫
        rX.normalization.adjunction.counit.app ((a.right.obj ((red l E b q rY).obj K)).obj)
  right_reduction' : ∀ K : sfIntegralConstructibleCategory l E Y',
    (exceptionalComparison'.hom.app K).hom =
      (spCompletedReduction l E X' (q.abelian X') rX'.reduction).map
          (rightLimit'.hom.app K) ≫
        rX'.normalization.adjunction.counit.app ((a.right'.obj ((red l E b q rY').obj K)).obj)
  counit : ∀ K : sfIntegralConstructibleCategory l E Y,
    (red l E b q rY).map (adjunction.counit.app K) =
      supportComparison.hom.app (right.obj K) ≫
        (SpTowerGluing.support l E b o q c a.support_closed).map
          (exceptionalComparison.hom.app K) ≫
        a.adjunction.counit.app ((red l E b q rY).obj K)
  counit' : ∀ K : sfIntegralConstructibleCategory l E Y',
    (red l E b q rY').map (adjunction'.counit.app K) =
      supportComparison'.hom.app (right'.obj K) ≫
        (SpTowerGluing.support l E b o q (c.ofIsPullback sq) a.support_closed').map
          (exceptionalComparison'.hom.app K) ≫
        a.adjunction'.counit.app ((red l E b q rY').obj K)
  pullModel : PullModel l E b o q u' rX' rX
  pullModel' : PullModel l E b o q v rY' rY
  pullLimit : constructibleIntegralPullback l E u' ⋙ (sfIntegralConstructible l E X').ι ≅
    red l E b q rX ⋙ SpTowerMate.U l E b o q a ⋙
      SpTowerCalculus.inclusion l E b q X' ⋙ lim l E b q rX'
  pullLimit' : constructibleIntegralPullback l E v ⋙ (sfIntegralConstructible l E Y').ι ≅
    red l E b q rY ⋙ SpTowerMate.V l E b o q a ⋙
      SpTowerCalculus.inclusion l E b q Y' ⋙ lim l E b q rY'
  pullComparison : constructibleIntegralPullback l E u' ⋙ red l E b q rX' ≅
    red l E b q rX ⋙ SpTowerMate.U l E b o q a
  pullComparison' : constructibleIntegralPullback l E v ⋙ red l E b q rY' ≅
    red l E b q rY ⋙ SpTowerMate.V l E b o q a
  pull_normalized : ∀ K : sfIntegralConstructibleCategory l E X,
    (pullComparison.hom.app K).hom = pullReduction l E b o q u' rX' rX pullModel K
  pull_normalized' : ∀ K : sfIntegralConstructibleCategory l E Y,
    (pullComparison'.hom.app K).hom = pullReduction l E b o q v rY' rY pullModel' K
  pull_counit : ∀ K : sfIntegralConstructibleCategory l E X,
    (pullComparison.hom.app K).hom =
      (spCompletedReduction l E X' (q.abelian X') rX'.reduction).map
          (pullLimit.hom.app K) ≫
        rX'.normalization.adjunction.counit.app
          (((SpTowerMate.U l E b o q a).obj ((red l E b q rX).obj K)).obj)
  pull_counit' : ∀ K : sfIntegralConstructibleCategory l E Y,
    (pullComparison'.hom.app K).hom =
      (spCompletedReduction l E Y' (q.abelian Y') rY'.reduction).map
          (pullLimit'.hom.app K) ≫
        rY'.normalization.adjunction.counit.app
          (((SpTowerMate.V l E b o q a).obj ((red l E b q rY).obj K)).obj)


end AlgebraicGeometry.ProEtale.SpExceptionalBaseChange
