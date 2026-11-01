/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CondensedExceptionalReconstruction.ExceptionalReconstructionPresentations
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
(blueprint: def-pur-exceptional-reconstruction-context).

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
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
attribute [local irreducible] CategoryTheory.mateEquiv CategoryTheory.conjugateEquiv
attribute [local irreducible] DerivedCategory.Q
  CategoryTheory.Functor.mapDerivedCategoryFactors
attribute [local irreducible]   AlgebraicGeometry.ProEtale.SemilinearProperOpen.R
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

variable (l : ℕ) [Fact l.Prime]
open AlgebraicGeometry.ProEtale.SemilinearProperOpen

attribute [local irreducible] realization complexSquare localizationSquare SequenceLocalization
  sectionValue

/-- Presentation transport of actual ordinary and derived inverse/direct images.
The section equation fixes the ordinary direct image; mates and the localization equation
fix the adjunction and derived comparisons, rather than choosing arbitrary isomorphisms.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-context). -/
structure SequenceImageBridge {T S : Scheme.{u}} (g : T ⟶ S)
    (PT : ExceptionalProEvaluation T (clopenSystemRing l (Field.{u} l))
      (clopenSystemUniformizer l (Field.{u} l)))
    (PS : ExceptionalProEvaluation S (clopenSystemRing l (Field.{u} l))
      (clopenSystemUniformizer l (Field.{u} l)))
    (O : ExceptionalProOrdinaryImage (clopenSystemRing l (Field.{u} l))
      (clopenSystemUniformizer l (Field.{u} l)) g)
    (I : SheafOfModules.CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology S) (K := Scheme.ProEt.topology T)
      _ _ _ _ _ O PS PT)
    (ST : ClopenSequenceRealization l (Field.{u} l) T)
    (SS : ClopenSequenceRealization l (Field.{u} l) S) where
  ordinaryDirect : O.rightSystem ⋙ SS.ordinary.functor ≅
    ST.ordinary.functor ⋙ push (quotientRings l (Field.{u} l))
      (quotientMaps l (Field.{u} l)) g
  sections : ∀ (M : ClopenProEtaleSystem l (Field.{u} l) T) (n : ℕ) (U : S.ProEt)
    (a : ((O.rightSystem ⋙ SS.ordinary.functor).obj M).val.obj (op (n, U)))
    (b : ((O.rightSystem.obj M).level n).val.obj (op U))
    (d : (ST.ordinary.functor.obj M).val.obj (op (n, (Scheme.proEtaleBaseChange g).obj U)))
    (e : (M.level n).val.obj (op ((Scheme.proEtaleBaseChange g).obj U))),
    sectionValue (((SS.evaluation n).hom.app (O.rightSystem.obj M)).val.app (op U)) a b →
    sectionValue ((ordinaryDirect.hom.app M).val.app (op (n, U))) a d →
    sectionValue (((ST.evaluation n).hom.app M).val.app
      (op ((Scheme.proEtaleBaseChange g).obj U))) d e →
    ∀ b' : ((O.right n).obj (M.level n)).val.obj (op U),
      sectionValue (((O.rightEvaluation n).hom.app M).val.app (op U)) b b' →
      sectionValue (((O.rightUnderlying n).hom.app (M.level n)).hom.app (op U)) b' e
  ordinaryPull : SS.ordinary.functor ⋙
      pull (quotientRings l (Field.{u} l)) (quotientMaps l (Field.{u} l)) g ≅
    O.inverse ⋙ ST.ordinary.functor
  ordinaryMate : (mateEquiv O.systemAdj
    (ordinaryAdj (quotientRings l (Field.{u} l)) (quotientMaps l (Field.{u} l)) g)
    (.mk _ _ _ _ ordinaryPull.hom)).natTrans = ordinaryDirect.hom
  derivedPull : SS.derived.functor ⋙
      P (quotientRings l (Field.{u} l)) (quotientMaps l (Field.{u} l)) g ≅
    I.system.inverse ⋙ ST.derived.functor
  localization : SequenceLocalization l g PT PS O I ST SS ordinaryPull derivedPull
  derivedDirect : I.system.direct ⋙ SS.derived.functor ≅
    ST.derived.functor ⋙ R (quotientRings l (Field.{u} l))
      (quotientMaps l (Field.{u} l)) g
  derivedMate : (mateEquiv I.system.adjunction
    (adj (quotientRings l (Field.{u} l)) (quotientMaps l (Field.{u} l)) g)
    (.mk _ _ _ _ derivedPull.hom)).natTrans = derivedDirect.hom

variable (k : Type u) [_root_.Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- The ordinary Brown adjunction, finite adjunctions, site comparisons and normalized
presentation transports for the fixed geometric compactification. These are construction
data to be supplied by the theorem, not extra hypotheses on a scheme morphism.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-context). -/
structure Context (X Y : Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f) where
  reduction : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l (Field.{u} l) W
  etale : StrictEtaleCompactSupport
    (clopenSystemRing l (Field.{u} l)) (clopenSystemUniformizer l (Field.{u} l)) c
  brown : EtaleTowerBrownAdjunction etale
  finite : StrictEtaleExceptionalAdjoint _ _ c etale
  source : ClopenSystemComparison l (Field.{u} l) X.scheme etale.PX
  target : ClopenSystemComparison l (Field.{u} l) Y.scheme etale.PY
  middle : ExceptionalSystemSiteComparison
    (clopenSystemRing l (Field.{u} l)) (clopenSystemUniformizer l (Field.{u} l)) c.Z etale.PZ
  support : ExceptionalProCompactSupport _ _ c
    source.proEtaleEvaluation target.proEtaleEvaluation middle.proEvaluation
  middleSequence : ClopenSequenceRealization l (Field.{u} l) c.Z
  properSequence : SequenceImageBridge l c.g middle.proEvaluation target.proEtaleEvaluation
    support.val.properImage support.val.properDerived middleSequence target.sequence
  openSequence : SequenceImageBridge l c.i source.proEtaleEvaluation middle.proEvaluation
    support.val.openImage support.val.openDerived source.sequence middleSequence
  openComparison : support.val.derivedOpen ⋙ middleSequence.derived.functor ≅
    source.sequence.derived.functor ⋙
      J (quotientRings l (Field.{u} l)) (quotientMaps l (Field.{u} l)) c.i
  openMate : (mateEquiv support.val.derivedOpenAdjunction
    (jAdj (quotientRings l (Field.{u} l)) (quotientMaps l (Field.{u} l)) c.i)
    (.mk _ _ _ _ openComparison.inv)).natTrans = openSequence.derivedPull.inv
  comparison : ExceptionalSystemCompactificationComparison etale
    ⟨source.proEtaleEvaluation, source.ordinary, source.derived⟩
    ⟨target.proEtaleEvaluation, target.ordinary, target.derived⟩ middle support

end WeilConjectures.CondensedExceptionalReconstruction
