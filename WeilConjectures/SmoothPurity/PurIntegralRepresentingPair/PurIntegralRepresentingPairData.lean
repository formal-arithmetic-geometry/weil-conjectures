/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurIntegralSupportComparison.PurIntegralSupportComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.GoodTruncationNormalization

/-! # Integral representing pairs from supplied exceptional systems

Source: blueprint, sec-smooth-purity/sk-prop-sp-integral-adjunction, Hom display
and unit/counit paragraph (blueprint: lem-pur-integral-reconstructed-representing-pair).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] WeilConjectures.integralExceptionalSystemDerived
attribute [-instance] WeilConjectures.integralExceptionalLevelDerived
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules
open WeilConjectures AlgebraicGeometry.Scheme
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
namespace WeilConjectures.PurIntegralRepresentingPair
open PurIntegralSupportComparison
attribute [local irreducible] Padic coordinates purCoefficientModel
  integralExceptionalCoordinates



variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Reduction followed by the existing exact quotient coordinates.
Source: blueprint integral Hom display
(blueprint: lem-pur-integral-reconstructed-representing-pair). -/
def reduction (W : Scheme.{u}) (R : CoefficientDerivedSystemCalculus l E W) :=
  (purCoefficientModel l E W).functor ⋙ R.reduction ⋙ (coordinates l E W).functor

/-- Total limit in the original completed-coefficient presentation.
Source: blueprint integral Hom display
(blueprint: lem-pur-integral-reconstructed-representing-pair). -/
def totalLimit (W : Scheme.{u}) :=
  (coordinates l E W).inverse ⋙ coefficientSequenceLimit l E W ⋙
    (purCoefficientModel l E W).inverse

/-- The actual adjunction, conjugated by the two fixed coefficient equivalences.
Source: blueprint integral Hom display and unit/counit paragraph
(blueprint: lem-pur-integral-reconstructed-representing-pair). -/
def adjunction (W : Scheme.{u}) (R : CoefficientDerivedSystemCalculus l E W) :
    reduction l E W R ⊣ totalLimit l E W :=
  ((purCoefficientModel l E W).toAdjunction.comp R.adjunction).comp
    (coordinates l E W).toAdjunction

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  (RX : CoefficientDerivedSystemCalculus l E X)
  (RY : CoefficientDerivedSystemCalculus l E Y)
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)
  (G : EtaleTowerBrownAdjunction S) (H : BrownTowerComparison.FiniteEvaluation S G)
  (D : BrownTowerComparison.TransportData S G H)

/-- Compact-support reconstruction is the actual reduction/proper-open/total-limit
composite, in the explicit semilinear coordinates. This is the same strict-system
construction as CompactSupportCondensedRealization.rawSupport.
Source: blueprint integral Hom display
(blueprint: lem-pur-integral-reconstructed-representing-pair). -/
def support := reduction l E X RX ⋙ D.compact.functor ⋙ totalLimit l E Y

/-- Transport the system proper/open comparison through the fixed quotient
coordinates and their actual equivalence unit. This comparison identifies the coordinate
expression with the dependency's published total-limit functor.
Source: blueprint compact-support reconstruction
(blueprint: lem-pur-integral-reconstructed-representing-pair). -/
def supportPresentation
    (beta : (coordinates l E X).functor ⋙ D.compact.functor ≅
      CompactSupportCondensedRealization.systemSupport l E c ⋙ (coordinates l E Y).functor) :
    support l E RX S G H D ≅
      CompactSupportCondensedRealization.rawSupport l E c RX :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft ((purCoefficientModel l E X).functor ⋙ RX.reduction) beta)
      (totalLimit l E Y) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft ((purCoefficientModel l E X).functor ⋙ RX.reduction ⋙
        CompactSupportCondensedRealization.systemSupport l E c)
        (coordinates l E Y).unitIso.symm)
      (coefficientSequenceLimit l E Y ⋙ (purCoefficientModel l E Y).inverse)

/-- The comparison alpha is the specified reduction/total-limit counit, rather than
an arbitrary isomorphism with the same endpoints.
Source: blueprint unit/counit paragraph
(blueprint: lem-pur-integral-reconstructed-representing-pair). -/
def alpha (K : PbcCompletedDerived X (Scheme.pbcIntegralDatum l E)) :=
  (adjunction l E Y RY).counit.app
    (D.compact.functor.obj ((reduction l E X RX).obj K))

/-- The Brown output is formed by the actual derived site direct image, Brown right
adjoint, and exact site inverse image, in that order.
Source: blueprint integral Hom display
(blueprint: lem-pur-integral-reconstructed-representing-pair). -/
def brown := D.siteY.direct ⋙ G.right ⋙ D.siteX.inverse

/-- The finite exceptional output at level n+1, in the dependency's ring-sheaf
presentation. Source: blueprint supplied-system hypothesis
(blueprint: lem-pur-integral-reconstructed-representing-pair). -/
def exceptionalLevel
    (L : CondensedERealization.Integral l E Y) (n : ℕ) :=
  (BrownTowerComparison.finiteExceptional S G H D.siteX D.siteY n).obj
    ((D.siteY.proEvaluation.evaluation n).obj ((reduction l E Y RY).obj L.obj))

/-- The finite identification written in Brown-output coordinates.
Source: blueprint proof Step 2, psi_n = c_n inverse phi_n
(blueprint: lem-pur-integral-reconstructed-representing-pair). -/
def levelMap (L : CondensedERealization.Integral l E Y)
    (V : DerivedCategory (BrownTowerComparison.ProSystem X
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)))
    (phi : ∀ n : ℕ, (D.siteX.proEvaluation.evaluation n).obj V ≅
      exceptionalLevel l E RY S G H D L n) (n : ℕ) :=
  (phi n).hom ≫ (D.evaluation n).inv.app ((reduction l E Y RY).obj L.obj)

attribute [local irreducible] coefficientSequenceLimit supportPresentation
  PurIntegralSupportComparison.beta
  PurIntegralSupportComparison.normalized

/-- The supplied normalized exceptional system, including its common finite interval,
intrinsic constructibility, quotient-transition squares and the two recognition modes.
The first mode supplies an actual system isomorphism; the second supplies a single degree.
Source: blueprint integral Hom display, ordinary-derived refinement, hypotheses
(blueprint: lem-pur-integral-reconstructed-representing-pair). -/
structure Supplied (L : CondensedERealization.Integral l E Y) where
  system : DerivedCategory (BrownTowerComparison.ProSystem X
    (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E))
  normalized : IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
    (J := Scheme.ProEt.topology X)
    (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)
      D.siteX.proEvaluation system
  bounds : ∃ a b : ℤ, ∀ n : ℕ,
    ((D.siteX.proEvaluation.evaluation n).obj system).IsGE a ∧
    ((D.siteX.proEvaluation.evaluation n).obj system).IsLE b
  constructible : ∀ n : ℕ, ∀ q : ℤ,
    @Scheme.IsConstructibleProEtaleFixedModuleSheaf.{u} X
      (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n) _ (D.finite n)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((D.siteX.realization n).derived.obj ((D.siteX.proEvaluation.evaluation n).obj system)))
  phi : ∀ n : ℕ, (D.siteX.proEvaluation.evaluation n).obj system ≅
    exceptionalLevel l E RY S G H D L n
  transition : ∀ (m n : ℕ) (h : n ≤ m),
    (D.siteX.proEvaluation.transition h).app system ≫
      (D.siteX.proEvaluation.scalar h).restriction.map
        (levelMap l E RY S G H D L system phi n) =
    levelMap l E RY S G H D L system phi m ≫
      (D.siteX.proEvaluation.transition h).app
        ((brown l E S G H D).obj ((reduction l E Y RY).obj L.obj))
  recognition :
    {theta : system ≅ (brown l E S G H D).obj ((reduction l E Y RY).obj L.obj) //
      ∀ n : ℕ, (D.siteX.proEvaluation.evaluation n).map theta.hom =
        levelMap l E RY S G H D L system phi n} ⊕
    {r : ℤ // ∀ n : ℕ,
      ((D.siteX.proEvaluation.evaluation n).obj system).IsGE r ∧
      ((D.siteX.proEvaluation.evaluation n).obj system).IsLE r}
  integral : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
    ((totalLimit l E X).obj system)
  reductions : ∀ n : ℕ, IsIso ((D.siteX.proEvaluation.evaluation n).map
    ((adjunction l E X RX).counit.app system))

/-- The supplied reconstructed object in the published full integral category.
Source: blueprint hypothesis M = total limit of the supplied system
(blueprint: lem-pur-integral-reconstructed-representing-pair). -/
def Supplied.object {L : CondensedERealization.Integral l E Y}
    (A : Supplied l E RX RY S G H D L) : CondensedERealization.Integral l E X :=
  ⟨(totalLimit l E X).obj A.system, A.integral⟩

/-- The actual Hom formula, with the reduction/limit counit and the actual Brown
counit. Inversion is only of the canonical unit, and its invertibility is asserted
in the conclusion below. Source: blueprint proof Step 4
(blueprint: lem-pur-integral-reconstructed-representing-pair). -/
def transpose (L : CondensedERealization.Integral l E Y)
    (A : Supplied l E RX RY S G H D L)
    (theta : A.system ≅ (brown l E S G H D).obj ((reduction l E Y RY).obj L.obj))
    (epsilon : D.compact.functor.obj
      ((brown l E S G H D).obj ((reduction l E Y RY).obj L.obj)) ⟶
        (reduction l E Y RY).obj L.obj)
    (hunit : IsIso ((adjunction l E Y RY).unit.app L.obj))
    (K : CondensedERealization.Integral l E X) (h : K ⟶ A.object) :
    (support l E RX S G H D).obj K.obj ⟶ L.obj :=
  letI := hunit
  (adjunction l E Y RY).unit.app ((support l E RX S G H D).obj K.obj) ≫
    (totalLimit l E Y).map
      (alpha l E RX RY S G H D K.obj ≫
        D.compact.functor.map ((reduction l E X RX).map h.hom ≫
          (adjunction l E X RX).counit.app A.system ≫ theta.hom) ≫ epsilon) ≫
    inv ((adjunction l E Y RY).unit.app L.obj)

/-- The single-degree normalization describes the actual good-truncation map by its
identity on cohomology. Uniqueness of this normalization is the heart embedding's
full faithfulness. Source: Stacks 06XS, 08J5; blueprint proof Step 2
(blueprint: lem-pur-integral-reconstructed-representing-pair). -/
def SingleDegreeNormalization (L : CondensedERealization.Integral l E Y)
    (A : Supplied l E RX RY S G H D L)
    (theta : A.system ≅ (brown l E S G H D).obj ((reduction l E Y RY).obj L.obj)) : Prop :=
  match A.recognition with
  | Sum.inl z => theta = z.val
  | Sum.inr z =>
    ∃ (a : (DerivedCategory.homologyFunctor _ z.val).obj A.system ≅
        (DerivedCategory.homologyFunctor _ z.val).obj
          ((brown l E S G H D).obj ((reduction l E Y RY).obj L.obj)))
      (deltaM : A.system ≅ (DerivedCategory.singleFunctor _ z.val).obj
        ((DerivedCategory.homologyFunctor _ z.val).obj A.system))
      (deltaN : (brown l E S G H D).obj ((reduction l E Y RY).obj L.obj) ≅
        (DerivedCategory.singleFunctor _ z.val).obj
          ((DerivedCategory.homologyFunctor _ z.val).obj
            ((brown l E S G H D).obj ((reduction l E Y RY).obj L.obj)))),
      (DerivedCategory.homologyFunctor _ z.val).map deltaM.hom ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso _ z.val).hom.app
            ((DerivedCategory.homologyFunctor _ z.val).obj A.system) = 𝟙 _ ∧
      (DerivedCategory.homologyFunctor _ z.val).map deltaN.hom ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso _ z.val).hom.app
            ((DerivedCategory.homologyFunctor _ z.val).obj
              ((brown l E S G H D).obj ((reduction l E Y RY).obj L.obj))) = 𝟙 _ ∧
      theta = deltaM ≪≫ (DerivedCategory.singleFunctor _ z.val).mapIso a ≪≫ deltaN.symm

/-- Coordinate identification with the ordinary finite exceptional functor, obtained
by pasting the recorded level site and finite Brown comparisons.
Source: blueprint proof Steps 1 and 6; Brown transport proof Step 8
(blueprint: lem-pur-integral-reconstructed-representing-pair). -/
def finiteCoordinates
    (hD : BrownTowerComparison.Transport S G H D (finite := D.finite)) (n : ℕ) :=
  letI : ∀ m, Finite (BrownTowerComparison.Ring
    (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) m) := D.finite
  let A := BrownTowerComparison.Ring (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) n
  Functor.isoWhiskerLeft
      ((D.siteY.comparison.evaluation.level n).direct ⋙ H.right n)
      (D.siteX.inverseLevel n) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (D.siteY.comparison.evaluation.level n).direct
        (eqToIso (congrArg (fun (R : BrownTowerComparison.Realization X.smallEtaleTopology
          (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n) ↦
            H.right n ⋙ R.derived) (hD.realizationX n)) ≪≫
          H.finiteRight n)) (FiniteCoefficientAdjoints.nu A X) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
        (eqToIso (congrArg
          (fun (R : BrownTowerComparison.Realization Y.smallEtaleTopology
            (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n) ↦
              (D.siteY.comparison.evaluation.level n).direct ⋙ R.derived)
          (hD.realizationY n).symm) ≪≫ D.siteY.directLevel n)
        (BrownTowerComparison.ordinaryFiniteRight A c)) (FiniteCoefficientAdjoints.nu A X)

/-- The actual finite counit, normalized by compact-support site comparison and the
ordinary finite etale adjunction, followed by the site-adjunction counit.
Source: blueprint unit/counit paragraph; finite-adjoint-comparisons normalization
(blueprint: lem-pur-integral-reconstructed-representing-pair). -/
def finiteCounit (n : ℕ)
    (C : DerivedCategory (BrownTowerComparison.ProSystem Y
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)))
    (hb : letI := D.finite n
      DerivedCategory.TStructure.t.plus
        ((BrownTowerComparison.ordinaryFiniteRight
          (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
            (integralExceptionalUniformizer l E) n) c).obj
          ((FiniteCoefficientAdjoints.rnu _ Y).obj
            ((D.siteY.realization n).derived.obj
              ((D.siteY.proEvaluation.evaluation n).obj C))))) :=
  letI := D.finite n
  let A := BrownTowerComparison.Ring (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) n
  let Q := (FiniteCoefficientAdjoints.rnu A Y).obj
    ((D.siteY.realization n).derived.obj ((D.siteY.proEvaluation.evaluation n).obj C))
  (ProEtale.compactSupportSiteComparison A c).hom.app
      ⟨(BrownTowerComparison.ordinaryFiniteRight A c).obj Q, hb⟩ ≫
    (FiniteCoefficientAdjoints.nu A Y).map
      ((BrownTowerComparison.ordinaryFiniteAdjunction A c).counit.app Q) ≫
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit.app
      ((D.siteY.realization n).derived.obj ((D.siteY.proEvaluation.evaluation n).obj C))

attribute [local irreducible] finiteCoordinates finiteCounit transpose
  SingleDegreeNormalization alpha BrownTowerComparison.ordinaryFiniteRight



/-- The representing pair at one supplied input, with its actual counit normalization.
All fields below are conclusions; no global constructible integral right adjoint is
assumed. Source: blueprint integral Hom display and unit/counit paragraph
(blueprint: lem-pur-integral-reconstructed-representing-pair). -/
structure Pair (L : CondensedERealization.Integral l E Y)
    (A : Supplied l E RX RY S G H D L)
    (hD : BrownTowerComparison.Transport S G H D (finite := D.finite)) where
  theta : A.system ≅ (brown l E S G H D).obj ((reduction l E Y RY).obj L.obj)
  theta_evaluation : ∀ n : ℕ, (D.siteX.proEvaluation.evaluation n).map theta.hom =
    levelMap l E RY S G H D L A.system A.phi n
  theta_normalization : SingleDegreeNormalization l E RX RY S G H D L A theta
  origin : D.siteY.Origin ((reduction l E Y RY).obj L.obj)
  normalized : IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
    (J := Scheme.ProEt.topology Y)
    (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)
      D.siteY.proEvaluation ((reduction l E Y RY).obj L.obj)
  finiteTor : ∀ n : ℕ,
    FiniteCoefficientAdjoints.ctf
      (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n) Y
      ((D.siteY.realization n).derived.obj
        ((D.siteY.proEvaluation.evaluation n).obj ((reduction l E Y RY).obj L.obj)))
  lowerBound : ∃ a : ℤ, ∀ n : ℕ, (exceptionalLevel l E RY S G H D L n).IsGE a
  unit_iso : IsIso ((adjunction l E Y RY).unit.app L.obj)
  support_integral : ∀ K : CondensedERealization.Integral l E X,
    PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)
      ((support l E RX S G H D).obj K.obj)
  alpha_iso : ∀ K : CondensedERealization.Integral l E X,
    IsIso (alpha l E RX RY S G H D K.obj)
  hom : ∀ K : CondensedERealization.Integral l E X,
    (K ⟶ A.object) ≃ₗ[PbcIntegralRing l E]
      ((support l E RX S G H D).obj K.obj ⟶ L.obj)
  hom_formula : ∀ K h, hom K h = transpose l E RX RY S G H D L A theta
    (D.counit _ origin normalized finiteTor lowerBound) unit_iso K h
  hom_natural : ∀ (K K' : CondensedERealization.Integral l E X) (b : K' ⟶ K) h,
    hom K' (b ≫ h) = (support l E RX S G H D).map b.hom ≫ hom K h
  trace_reduction :
    (reduction l E Y RY).map (hom A.object (𝟙 A.object)) =
      alpha l E RX RY S G H D A.object.obj ≫
        D.compact.functor.map ((adjunction l E X RX).counit.app A.system) ≫
        D.compact.functor.map theta.hom ≫
        D.counit _ origin normalized finiteTor lowerBound
  finite_etale_bound : ∀ n : ℕ, letI := D.finite n
    DerivedCategory.TStructure.t.plus
      ((BrownTowerComparison.ordinaryFiniteRight
        (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n) c).obj
        ((FiniteCoefficientAdjoints.rnu _ Y).obj
          ((D.siteY.realization n).derived.obj
            ((D.siteY.proEvaluation.evaluation n).obj ((reduction l E Y RY).obj L.obj)))))
  trace_evaluation : ∀ n : ℕ,
    (D.siteY.realization n).derived.map ((D.siteY.proEvaluation.evaluation n).map
      ((reduction l E Y RY).map (hom A.object (𝟙 A.object)))) =
    (D.siteY.realization n).derived.map ((D.siteY.proEvaluation.evaluation n).map
      (alpha l E RX RY S G H D A.object.obj ≫
        D.compact.functor.map ((adjunction l E X RX).counit.app A.system))) ≫
      (D.compactEvaluation n).hom.app A.system ≫
      (FiniteCoefficientAdjoints.lower
        (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n) c).map
        ((D.siteX.realization n).derived.map (A.phi n).hom ≫
          (finiteCoordinates l E S G H D hD n).hom.app
            ((D.siteY.proEvaluation.evaluation n).obj ((reduction l E Y RY).obj L.obj))) ≫
      finiteCounit l E S G H D n ((reduction l E Y RY).obj L.obj) (finite_etale_bound n)

/-- Naturality of the pairs and traces on actual supplied system maps. The same-degree
clause only uses level squares for concentrated systems, never levelwise faithfulness
on arbitrary derived systems. Source: blueprint proof Steps 2 and 7
(blueprint: lem-pur-integral-reconstructed-representing-pair). -/
structure Family
    (hD : BrownTowerComparison.Transport S G H D (finite := D.finite)) where
  pair : ∀ (L : CondensedERealization.Integral l E Y)
    (A : Supplied l E RX RY S G H D L), Pair l E RX RY S G H D L A hD
  hom_natural : ∀ (L L' : CondensedERealization.Integral l E Y)
    (A : Supplied l E RX RY S G H D L) (A' : Supplied l E RX RY S G H D L')
    (b : L ⟶ L') (a : A.system ⟶ A'.system),
    a ≫ (pair L' A').theta.hom = (pair L A).theta.hom ≫
      (brown l E S G H D).map ((reduction l E Y RY).map b.hom) →
    ∀ (K : CondensedERealization.Integral l E X) (h : K ⟶ A.object),
      (pair L' A').hom K
          (ObjectProperty.homMk (h.hom ≫ (totalLimit l E X).map a)) =
        (pair L A).hom K h ≫ b.hom
  trace_natural : ∀ (L L' : CondensedERealization.Integral l E Y)
    (A : Supplied l E RX RY S G H D L) (A' : Supplied l E RX RY S G H D L')
    (b : L ⟶ L') (a : A.system ⟶ A'.system),
    a ≫ (pair L' A').theta.hom = (pair L A).theta.hom ≫
      (brown l E S G H D).map ((reduction l E Y RY).map b.hom) →
    (support l E RX S G H D).map ((totalLimit l E X).map a) ≫
      (pair L' A').hom A'.object (𝟙 A'.object) =
        (pair L A).hom A.object (𝟙 A.object) ≫ b.hom
  single_degree_square : ∀ (L L' : CondensedERealization.Integral l E Y)
    (A : Supplied l E RX RY S G H D L) (A' : Supplied l E RX RY S G H D L')
    (r : ℤ),
    ∀ (b : L ⟶ L') (a : A.system ⟶ A'.system),
    (∀ n, ((D.siteX.proEvaluation.evaluation n).obj A.system).IsGE r ∧
      ((D.siteX.proEvaluation.evaluation n).obj A.system).IsLE r) →
    (∀ n, ((D.siteX.proEvaluation.evaluation n).obj A'.system).IsGE r ∧
      ((D.siteX.proEvaluation.evaluation n).obj A'.system).IsLE r) →
    (∀ n, (D.siteX.proEvaluation.evaluation n).map a ≫
      levelMap l E RY S G H D L' A'.system A'.phi n =
        levelMap l E RY S G H D L A.system A.phi n ≫
          (D.siteX.proEvaluation.evaluation n).map
            ((brown l E S G H D).map ((reduction l E Y RY).map b.hom))) →
    a ≫ (pair L' A').theta.hom = (pair L A).theta.hom ≫
      (brown l E S G H D).map ((reduction l E Y RY).map b.hom)





end WeilConjectures.PurIntegralRepresentingPair
