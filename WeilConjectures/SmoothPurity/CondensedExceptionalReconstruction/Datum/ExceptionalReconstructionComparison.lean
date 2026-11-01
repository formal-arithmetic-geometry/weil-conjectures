/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CondensedExceptionalReconstruction.ExceptionalReconstructionContext
public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERealizationDefinitions
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointComparisons
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemTransport
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleTowerBrownAdjunction
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Clopen.ClopenStrictSystemComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CompactSupportCondensedRealization
import WeilConjectures.SmoothPurity.FilteredCondensedRepresentingPair.FilteredCondensedRepresentingPair
import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import WeilConjectures.CategoryTheory.Derived.DerivedMorphismPresheaf
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFlatCoefficientCalculus
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible

/-! # Condensed exceptional inverse image from an ordinary coefficient system

Source: current blueprint sec-smooth-purity, sk-prop-sp-integral-adjunction,
sk-prop-sp-rational, sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical;
WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/UpperShriek.lean,
`boundedConstructibleUpperShriekOfCompactification` and its specifying adjunction.
(blueprint: def-pur-exceptional-reconstruction-comparison).

The coefficient field is the canonical universe lift of Q_l. All systems below are
objects of ordinary derived categories of strict varying-coefficient module sheaves.
The helper records package the constructions and clauses of this node. In particular
no ambient unbounded pro-etale exceptional right adjoint is assumed or constructed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance high] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleLevelDerived
attribute [local semireducible] AlgebraicGeometry.exceptionalProSystemDerived
  AlgebraicGeometry.exceptionalProLevelDerived
attribute [local instance high] CategoryTheory.Functor.preservesZeroMorphisms_of_additive
attribute [local instance high] AlgebraicGeometry.ProEtale.SemilinearProperOpen.pull_additive
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.pull_limits
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.pull_colimits
  SheafOfModules.CoefficientSystemOrdinaryImage.systemInverseAdditive
  SheafOfModules.CoefficientSystemOrdinaryImage.inverseAdditive
  WeilConjectures.PurityFiniteSetting.ClopenSequenceRealizationData.ordinaryAdditive
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
attribute [local irreducible] CategoryTheory.mateEquiv CategoryTheory.conjugateEquiv
attribute [local irreducible] DerivedCategory.Q
  CategoryTheory.Functor.mapDerivedCategoryFactors
attribute [local irreducible] AlgebraicGeometry.ProEtale.SemilinearProperOpen.J
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.R
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.adj
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.rightAdjoint CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactification
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperShriekOfCompactification
universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedExceptionalReconstruction
open CondensedERealization CompactSupportCondensedRealization PurityFiniteSetting

variable (l : ℕ) [Fact l.Prime] (k : Type u) [_root_.Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  (D : CondensedERealization.Data l (Field.{u} l) k)
open AlgebraicGeometry.ProEtale.SemilinearProperOpen

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [local irreducible] WeilConjectures.purCoefficientModel

/-- The actual reduction of an integral input, transported to ordinary etale systems.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def input {X Y : Base k} {f : X.scheme ⟶ Y.scheme}
    [f.IsOver (Spec (.of k))] {c : Compactification f}
    (P : Context l k X Y f c) : Integral l (Field.{u} l) Y.scheme ⥤
      DerivedCategory (strictEtaleCoefficientSystem Y.scheme
        (clopenSystemRing l (Field.{u} l)) (clopenSystemUniformizer l (Field.{u} l))) :=
  ObjectProperty.ι (PbcIsBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l (Field.{u} l))) ⋙
    (purCoefficientModel l (Field.{u} l) Y.scheme).functor ⋙
      (P.reduction Y.scheme).reduction ⋙ P.target.sequence.derived.inverse ⋙
        P.target.derived.system.direct

/-- The actual pro-etale reduction system of the integral input.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def reduced {X Y : Base k} {f : X.scheme ⟶ Y.scheme}
    [f.IsOver (Spec (.of k))] {c : Compactification f}
    (P : Context l k X Y f c) (L : Integral l (Field.{u} l) Y.scheme) :=
  P.target.sequence.derived.inverse.obj
    ((P.reduction Y.scheme).reduction.obj
      ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj L.obj))

/-- N is inverse site image of the etale Brown right adjoint applied to the direct
site image of the actual reduction. Its boundedness is asserted only for admissible data.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def brownTower {X Y : Base k} {f : X.scheme ⟶ Y.scheme}
    [f.IsOver (Spec (.of k))] {c : Compactification f}
    (P : Context l k X Y f c) (L : Integral l (Field.{u} l) Y.scheme) :=
  P.source.derived.system.inverse.obj (P.brown.right.obj
    (P.target.derived.system.direct.obj (reduced l k P L)))

/-- Finite exceptional inverse image is the etale compact-support right adjoint
transported using the recorded finite-level site adjunction.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def finiteUpper {X Y : Base k} {f : X.scheme ⟶ Y.scheme}
    [f.IsOver (Spec (.of k))] {c : Compactification f}
    (P : Context l k X Y f c) (n : ℕ) :=
  (P.target.derived.level n).direct ⋙ P.finite.levelRight n ⋙
    (P.source.derived.level n).inverse

/-- The finite-level identification of the Brown output, using evaluation and the
unique counit-preserving comparison between the two ordinary etale right adjoints.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def brownLevel {X Y : Base k} {f : X.scheme ⟶ Y.scheme}
    [f.IsOver (Spec (.of k))] {c : Compactification f}
    (P : Context l k X Y f c) (L : Integral l (Field.{u} l) Y.scheme) (n : ℕ) :
    (P.source.proEtaleEvaluation.evaluation n).obj (brownTower l k P L) ≅
      (finiteUpper l k P n).obj
        ((P.target.proEtaleEvaluation.evaluation n).obj (reduced l k P L)) :=
  (SheafOfModules.CoefficientSystemDerivedImage.inverseEvaluation.{u + 1, u, u + 1, u, u + 1, u + 2}
    P.source.derived n).app _ ≪≫
    (P.source.derived.level n).inverse.mapIso
      ((P.etale.PX.evaluation n).mapIso
        ((P.brown.adjunction.rightAdjointUniq P.finite.adjunction).app _) ≪≫
        (P.finite.evaluation n).app _ ≪≫
        (P.finite.levelRight n).mapIso
      ((SheafOfModules.CoefficientSystemDerivedImage.directEvaluation
        P.target.derived n).app _))

/-- A supplied ordinary derived system M and its specified finite exceptional-image
identifications phi_n, together with the integral input L.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
structure Datum {X Y : Base k} {f : X.scheme ⟶ Y.scheme}
    [f.IsOver (Spec (.of k))] {c : Compactification f}
    (P : Context l k X Y f c) where
  L : Integral l (Field.{u} l) Y.scheme
  tower : DerivedCategory (ClopenProEtaleSystem l (Field.{u} l) X.scheme)
  phi : ∀ n : ℕ, (P.source.proEtaleEvaluation.evaluation n).obj tower ≅
    (finiteUpper l k P n).obj
      ((P.target.proEtaleEvaluation.evaluation n).obj (reduced l k P L))

variable {X Y : Base k} {f : X.scheme ⟶ Y.scheme}
  [f.IsOver (Spec (.of k))] {c : Compactification f}
  {P : Context l k X Y f c}

/-- The supplied finite identification expressed in the finite evaluation of N.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def Datum.toBrown (d : Datum l k P) (n : ℕ) :=
  d.phi n ≪≫ (brownLevel l k P d.L n).symm

/-- The actual semilinear transition squares, including every quotient n <= m.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def Datum.Transitions (d : Datum l k P) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m),
    (P.source.proEtaleEvaluation.transition h).app d.tower ≫
      (P.source.proEtaleEvaluation.scalar h).restriction.map (d.toBrown l k n).hom =
    (d.toBrown l k m).hom ≫
      (P.source.proEtaleEvaluation.transition h).app (brownTower l k P d.L)

/-- Normalization uses invertibility of the actual derived transition adjoints,
with the quotient cocycle supplied by the recorded system evaluation package.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def Datum.Normalized (d : Datum l k P) : Prop :=
  SheafOfModules.IsNormalizedCoefficientSystem
    (J := Scheme.ProEt.topology X.scheme)
    (clopenSystemRing l (Field.{u} l)) (clopenSystemUniformizer l (Field.{u} l))
    P.source.proEtaleEvaluation d.tower

/-- A common finite cohomological interval and intrinsic finite-stratification
constructibility at every positive coefficient level; no common stratification is required.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def Datum.BoundedConstructible (d : Datum l k P) : Prop :=
  (∃ a b : ℤ, ∀ n : ℕ,
    ((P.source.proEtaleEvaluation.evaluation n).obj d.tower).IsGE a ∧
      ((P.source.proEtaleEvaluation.evaluation n).obj d.tower).IsLE b) ∧
    ∀ n : ℕ, Scheme.intrinsicFiniteTorsionConstructible
      l (Field.{u} l) (n + 1) (Nat.succ_pos n) X.scheme
      ((coefficientSequenceDerivedEvaluation l (Field.{u} l) X.scheme n).obj
        (P.source.sequence.derived.functor.obj d.tower))

/-- The actual total right derived inverse limit after coefficient restriction.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def Datum.limit (d : Datum l k P) :=
  (coefficientSequenceLimit l (Field.{u} l) X.scheme).obj
    (P.source.sequence.derived.functor.obj d.tower)

/-- The actual limit belongs to the integral category and the actual reduction/limit
counit identifies its canonical reductions with the supplied system.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def Datum.Reconstructs (d : Datum l k P) : Prop :=
  PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l (Field.{u} l))
    ((purCoefficientModel l (Field.{u} l) X.scheme).inverse.obj (d.limit l k)) ∧
    IsIso ((P.reduction X.scheme).adjunction.counit.app
      (P.source.sequence.derived.functor.obj d.tower))

/-- The real total-limit construction regarded as an object of the integral full category.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def Datum.integral (d : Datum l k P) (h : d.Reconstructs l k) :
    Integral l (Field.{u} l) X.scheme :=
  ⟨(purCoefficientModel l (Field.{u} l) X.scheme).inverse.obj (d.limit l k), h.1⟩

/-- A genuine derived-system map induces the map of reconstructed integral objects.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def Datum.LimitMap {d e : Datum l k P}
    (a : d.tower ⟶ e.tower) (hd : d.Reconstructs l k) (he : e.Reconstructs l k) :
    d.integral l k hd ⟶ e.integral l k he :=
  ObjectProperty.homMk ((purCoefficientModel l (Field.{u} l) X.scheme).inverse.map
    ((coefficientSequenceLimit l (Field.{u} l) X.scheme).map
      (P.source.sequence.derived.functor.map a)))

/-- The square with the Brown towers for an actual derived-system map and an integral
input map; no lifting of arbitrary levelwise derived maps is assumed.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def Datum.SystemMap {d e : Datum l k P} (b : d.L ⟶ e.L) (a : d.tower ⟶ e.tower)
    (td : d.tower ≅ brownTower l k P d.L) (te : e.tower ≅ brownTower l k P e.L) : Prop :=
  a ≫ te.hom = td.hom ≫
    (P.source.derived.system.inverse.map (P.brown.right.map ((input l k P).map b)))

/-- The proper/open whole-system functor transported through the normalized strict-system
presentation comparisons. Its proper comparison is the specified derived mate.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def supportSequence (Q : Context l k X Y f c) :=
  pasteComparisons Q.support.val.derivedOpen Q.support.val.properDerived.system.direct
    Q.source.sequence.derived.functor Q.middleSequence.derived.functor
    Q.target.sequence.derived.functor
    Q.properSequence.derivedDirect Q.openComparison

/-- The actual ordinary tower counit: transpose the supplied system map under Brown,
then transport through the site unit/counit and the canonical compact-support comparison.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def Datum.proCounit (d : Datum l k P)
    (theta : d.tower ≅ brownTower l k P d.L)
    (hunit : IsIso (P.source.derived.system.adjunction.unit.app
      (P.brown.right.obj ((input l k P).obj d.L))))
    (hcomparison : IsIso ((exceptionalSystemOriginComparison P.comparison).app d.tower)) :
    (exceptionalProSupport P.support).obj d.tower ⟶ reduced l k P d.L :=
  @inv _ _ _ _ ((exceptionalSystemOriginComparison P.comparison).app d.tower) hcomparison ≫
    P.target.derived.system.inverse.map
      ((P.brown.adjunction.homEquiv _ _).symm
        (P.source.derived.system.direct.map theta.hom ≫
          @inv _ _ _ _ (P.source.derived.system.adjunction.unit.app _) hunit)) ≫
    P.target.derived.system.adjunction.counit.app (reduced l k P d.L)

/-- The same actual tower counit expressed on the ringed sequence site.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def Datum.sequenceCounit (d : Datum l k P)
    (theta : d.tower ≅ brownTower l k P d.L)
    (hunit : IsIso (P.source.derived.system.adjunction.unit.app
      (P.brown.right.obj ((input l k P).obj d.L))))
    (hcomparison : IsIso ((exceptionalSystemOriginComparison P.comparison).app d.tower)) :
    (systemSupport l (Field.{u} l) c).obj
      (P.source.sequence.derived.functor.obj d.tower) ⟶
        (P.reduction Y.scheme).reduction.obj
          ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj d.L.obj) :=
  (supportSequence l k P).inv.app d.tower ≫
    P.target.sequence.derived.functor.map (d.proCounit l k theta hunit hcomparison) ≫
    P.target.sequence.derived.counitIso.hom.app _

/-- Reconstruct the tower counit by the actual total limit and the inverse of the
canonical reconstruction unit. Both coefficient-presentation comparisons are retained.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def Datum.integralCounit (d : Datum l k P) (hd : d.Reconstructs l k)
    (A : RealizationAt l (Field.{u} l) k D P.reduction X Y f c)
    (hreduction : IsIso ((P.reduction Y.scheme).adjunction.unit.app
      ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj d.L.obj)))
    (theta : d.tower ≅ brownTower l k P d.L)
    (hunit : IsIso (P.source.derived.system.adjunction.unit.app
      (P.brown.right.obj ((input l k P).obj d.L))))
    (hcomparison : IsIso ((exceptionalSystemOriginComparison P.comparison).app d.tower)) :
    (integralSupport l (Field.{u} l) c P.reduction A.integral).obj
      (d.integral l k hd) ⟶ d.L :=
  ObjectProperty.homMk ((purCoefficientModel l (Field.{u} l) Y.scheme).inverse.map
    ((coefficientSequenceLimit l (Field.{u} l) Y.scheme).map
      ((systemSupport l (Field.{u} l) c).map
        ((P.reduction X.scheme).reduction.map
          ((purCoefficientModel l (Field.{u} l) X.scheme).counitIso.hom.app (d.limit l k)) ≫
            (P.reduction X.scheme).adjunction.counit.app
              (P.source.sequence.derived.functor.obj d.tower)) ≫
        d.sequenceCounit l k theta hunit hcomparison) ≫
      @inv _ _ _ _ ((P.reduction Y.scheme).adjunction.unit.app
        ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj d.L.obj)) hreduction) ≫
    (purCoefficientModel l (Field.{u} l) Y.scheme).unitIso.inv.app d.L.obj)

/-- Realize the reconstructed integral counit through the specified rational comparison.
Source: current blueprint sk-prop-sp-integral-adjunction and sk-prop-sp-rational.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def Datum.realizedCounit (d : Datum l k P) (hd : d.Reconstructs l k)
    (A : RealizationAt l (Field.{u} l) k D P.reduction X Y f c)
    (hreduction : IsIso ((P.reduction Y.scheme).adjunction.unit.app
      ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj d.L.obj)))
    (theta : d.tower ≅ brownTower l k P d.L)
    (hunit : IsIso (P.source.derived.system.adjunction.unit.app
      (P.brown.right.obj ((input l k P).obj d.L))))
    (hcomparison : IsIso ((exceptionalSystemOriginComparison P.comparison).app d.tower)) :=
  A.realization.inv.app
    ((pbcRationalization X.scheme (pbcIntegralDatum l (Field.{u} l))
      (pbcUniformizer l (Field.{u} l))).obj (d.integral l k hd)) ≫
    ((D.atObject Y).realization.functor ⋙
      (boundedConstructible (Coefficient (Field.{u} l) Y.scheme)).ι).map
      ((pbcRationalization Y.scheme (pbcIntegralDatum l (Field.{u} l))
        (pbcUniformizer l (Field.{u} l))).map
          (d.integralCounit l k D hd A hreduction theta hunit hcomparison))

set_option allowUnsafeReducibility true in
attribute [local irreducible] CondensedRing.rightDerivedLowerShriekOfCompactification

attribute [local irreducible] Datum.realizedCounit
  condensedScalar condensedProjection

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Scalar extension of the specified realized reconstruction counit.
Source: current blueprint sk-thm-sp-qbar, scalar extension of the representing pair.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def Datum.extendedCounit (d : Datum l k P) (hd : d.Reconstructs l k)
    (A : RealizationAt l (Field.{u} l) k D P.reduction X Y f c)
    (hreduction : IsIso ((P.reduction Y.scheme).adjunction.unit.app
      ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj d.L.obj)))
    (theta : d.tower ≅ brownTower l k P d.L)
    (hunit : IsIso (P.source.derived.system.adjunction.unit.app
      (P.brown.right.obj ((input l k P).obj d.L))))
    (hcomparison : IsIso ((exceptionalSystemOriginComparison P.comparison).app d.tower)) :=
  (omegaScalar l (Field.{u} l) (embedding l) Y.scheme).map
    (d.realizedCounit l k D hd A hreduction theta hunit hcomparison)

/-- Projection and scalar extension of the specified realized reconstruction counit.
Source: current blueprint sk-thm-sp-qbar, scalar extension of the representing pair.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def Datum.projectedCounit (d : Datum l k P) (hd : d.Reconstructs l k)
    (A : RealizationAt l (Field.{u} l) k D P.reduction X Y f c)
    (hreduction : IsIso ((P.reduction Y.scheme).adjunction.unit.app
      ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj d.L.obj)))
    (theta : d.tower ≅ brownTower l k P d.L)
    (hunit : IsIso (P.source.derived.system.adjunction.unit.app
      (P.brown.right.obj ((input l k P).obj d.L))))
    (hcomparison : IsIso ((exceptionalSystemOriginComparison P.comparison).app d.tower)) :=
    @inv _ _ _ _ ((condensedProjection (omegaMap l (Field.{u} l) (embedding l)) c).app
      ((D.atObject X).realization.functor.obj
        ((pbcRationalization X.scheme (pbcIntegralDatum l (Field.{u} l))
          (pbcUniformizer l (Field.{u} l))).obj (d.integral l k hd))).obj)
      (omegaProjection_isIso l (Field.{u} l) k (embedding l) X Y f c _) ≫
    d.extendedCounit l k D hd A hreduction theta hunit hcomparison

/-- Raw localization and closure scalar extension of the reconstructed finite counit,
preceded by the inverse of the specified compact-support projection comparison.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def Datum.condensedCounit (d : Datum l k P) (hd : d.Reconstructs l k)
    (A : RealizationAt l (Field.{u} l) k D P.reduction X Y f c)
    (hreduction : IsIso ((P.reduction Y.scheme).adjunction.unit.app
      ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj d.L.obj)))
    (theta : d.tower ≅ brownTower l k P d.L)
    (hunit : IsIso (P.source.derived.system.adjunction.unit.app
      (P.brown.right.obj ((input l k P).obj d.L))))
    (hcomparison : IsIso ((exceptionalSystemOriginComparison P.comparison).app d.tower)) :
    (CondensedRing.boundedConstructibleLowerShriekOfCompactification l (f := X.map Y f) c).obj
        ((realization l k D X).obj (d.integral l k hd)) ⟶
      (realization l k D Y).obj d.L :=
  ObjectProperty.homMk
    ((CondensedRing.boundedConstructibleLowerShriekOfCompactificationCompatibility l (f := X.map Y f) c).hom.app
        ((realization l k D X).obj (d.integral l k hd)) ≫
      d.projectedCounit l k D hd A hreduction theta hunit hcomparison)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The adjunction transpose of the explicitly reconstructed counit for the exact
chosen bounded constructible exceptional functor of the upstream declaration.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def Datum.comparison (d : Datum l k P) (hd : d.Reconstructs l k)
    (A : RealizationAt l (Field.{u} l) k D P.reduction X Y f c)
    (hreduction : IsIso ((P.reduction Y.scheme).adjunction.unit.app
      ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj d.L.obj)))
    (theta : d.tower ≅ brownTower l k P d.L)
    (hunit : IsIso (P.source.derived.system.adjunction.unit.app
      (P.brown.right.obj ((input l k P).obj d.L))))
    (hcomparison : IsIso ((exceptionalSystemOriginComparison P.comparison).app d.tower)) :=
  (CondensedRing.boundedConstructibleUpperShriekOfCompactificationAdjunction l (f := X.map Y f) c).homEquiv _ _
      (d.condensedCounit l k D hd A hreduction theta hunit hcomparison)

/-- Either the specified actual system isomorphism is supplied, or every level is
concentrated in a single specified integer degree. The second alternative adds no
system-isomorphism hypothesis: its construction by good truncation is a conclusion.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
inductive Datum.Alternative (d : Datum l k P) where
  | supplied (theta : d.tower ≅ brownTower l k P d.L)
      (levels : ∀ n : ℕ, (P.source.proEtaleEvaluation.evaluation n).map theta.hom =
        (d.toBrown l k n).hom)
  | single (r : ℤ) (degrees : ∀ n : ℕ,
      ((P.source.proEtaleEvaluation.evaluation n).obj d.tower).IsGE r ∧
        ((P.source.proEtaleEvaluation.evaluation n).obj d.tower).IsLE r)

/-- Case (a) retains exactly the supplied isomorphism; case (b) requires its
component maps, which determine the good-truncation system isomorphism uniquely.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
def Datum.Alternative.Uses {d : Datum l k P} (a : d.Alternative l k)
    (theta : d.tower ≅ brownTower l k P d.L) : Prop :=
  match a with
  | .supplied t _ => theta = t
  | .single _ _ => ∀ n : ℕ,
    (P.source.proEtaleEvaluation.evaluation n).map theta.hom = (d.toBrown l k n).hom

/-- Exactly the supplied-system hypotheses: normalization, transition compatibility,
the two alternatives, intrinsic uniform constructibility, and actual reconstruction.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
structure Datum.Admissible (d : Datum l k P) where
  normalized : d.Normalized l k
  transitions : d.Transitions l k
  alternative : d.Alternative l k
  constructible : d.BoundedConstructible l k
  reconstructs : d.Reconstructs l k

/-- The constructed system identification, bounded site transport, and invertibility
of the transpose of the specified counit. In the supplied alternative its identification
is the one supplied; in the single-degree alternative it has the prescribed evaluations.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
structure Conclusion (d : Datum l k P) (h : d.Admissible l k)
    (A : RealizationAt l (Field.{u} l) k D P.reduction X Y f c) where
  theta : d.tower ≅ brownTower l k P d.L
  supplied : h.alternative.Uses l k theta
  brownBound : ∃ a : ℤ, (brownTower l k P d.L).IsGE a
  levels : ∀ n : ℕ,
    (P.source.proEtaleEvaluation.evaluation n).map theta.hom = (d.toBrown l k n).hom
  reduction : IsIso ((P.reduction Y.scheme).adjunction.unit.app
    ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj d.L.obj))
  originUnit : IsIso (P.source.derived.system.adjunction.unit.app
    (P.brown.right.obj ((input l k P).obj d.L)))
  originSupport : IsIso ((exceptionalSystemOriginComparison P.comparison).app d.tower)
  invertible : IsIso (d.comparison l k D h.reconstructs A reduction theta originUnit originSupport)

/-- The isomorphism whose hom is literally the specified adjunction comparison map.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-comparison). -/
abbrev Conclusion.iso {d : Datum l k P} {h : d.Admissible l k}
    {A : RealizationAt l (Field.{u} l) k D P.reduction X Y f c}
    (q : Conclusion l k D d h A) :=
  @asIso _ _ _ _ (d.comparison l k D h.reconstructs A q.reduction q.theta
    q.originUnit q.originSupport) q.invertible

end WeilConjectures.CondensedExceptionalReconstruction
