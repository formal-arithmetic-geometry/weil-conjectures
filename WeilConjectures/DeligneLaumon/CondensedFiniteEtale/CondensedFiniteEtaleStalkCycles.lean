/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.FiniteEtaleStalk
public import WeilConjectures.TraceFormula.PointFiberFunctor
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteGenericFiberStratumInteriors
import WeilConjectures.AlgebraicGeometry.FiniteEtaleNoetherianClopenAssembly
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackConstantModelConstructible
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Homeomorph.Defs
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFiniteModelProofAPISupplement
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointDiscreteConstantComparison
public import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import WeilConjectures.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget
public import WeilConjectures.AlgebraicGeometry.UniversallyHomeomorphIntegral
public import WeilConjectures.CategoryTheory.Right.RightDerivedSingleH0
public import WeilConjectures.Mathlib.RingTheory.Etale.Field
public import WeilConjectures.ProperBaseChange.GeometricFieldProfiniteDenseSubsite
public import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.PullbackProfinite
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.RingTheory.ProEtale.WeakDimension
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.RingTheory.WContractibleGeometricCriterion
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedExchangeOpenRestriction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperConstructibleCohomology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRationalPushforward
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeil.CondensedStrictWeilComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-! # Condensed finite etale stalk cycles

Source: latest blueprint, sec-deligne-laumon-a1/sk-lem-wft-finite-map,
lem-a1-finite-map-purity.proof.md, first paragraph; Stacks 03QP(1), with the
condensed and Weil refinement recorded in the DAG
(blueprint: lem-a1-condensed-finite-etale-stalk-cycles).

The coefficient field is the standard chosen algebraic closure, with its universe lift.
All fibres are the existing point-sections functor applied to module pullback. All
restriction arrows are the existing adjunction-counit arrows. The local operators below
are the degree-zero specialization of the recorded local-return convention: the canonical
point reparametrization, pullback composition, and the iterated Weil isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj DirectSum

namespace WeilConjectures.CondensedFiniteEtale

open WeilConjectures.CondensedModule

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The existing base-change functor applied to g_0.
Source: blueprint geometric base change (blueprint: lem-a1-condensed-finite-etale-stalk-cycles).
-/
def geometricMap (g₀ : X₀ ⟶ Y₀) :
    (D.geometricFiber X₀).left ⟶ (D.geometricFiber Y₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map g₀).left

/-- The ordinary module direct image, including its canonical coefficient action.
Source: blueprint definition G=g_*F; det-def-sfb-module-pushforward-pullback
(blueprint: lem-a1-condensed-finite-etale-stalk-cycles). -/
def directImage (g₀ : X₀ ⟶ Y₀) (M : Modules l (D.geometricFiber X₀).left) :=
  (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) (geometricMap D g₀)).obj M

/-- The specified exchange followed by g_*theta, with no choice of a Weil structure.
Source: blueprint Weil-structure clause
(blueprint: lem-a1-condensed-finite-etale-stalk-cycles). -/
def directImageWeil (g₀ : X₀ ⟶ Y₀)
    (h : (D.geometricFrobenius X₀).hom ≫ geometricMap D g₀ =
      geometricMap D g₀ ≫ (D.geometricFrobenius Y₀).hom)
    (M : Modules l (D.geometricFiber X₀).left)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom).obj M ≅ M) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius Y₀).hom).obj (directImage D l g₀ M) ≅ directImage D l g₀ M :=
  (asIso (CondensedRing.lowerStarBaseChange (Profinite.padicAlgClRingObj l)
    (CommSq.mk h))).app M ≪≫
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) (geometricMap D g₀)).mapIso θ

/-- The actual points of the model above y, without a closedness assumption on them.
Source: blueprint S_y (blueprint: lem-a1-condensed-finite-etale-stalk-cycles). -/
abbrev ModelPoints (g₀ : X₀ ⟶ Y₀) (y : Y₀.left) := {x : X₀.left // g₀.left x = y}

/-- The residue degree for the canonical map kappa(y) to kappa(x).
Source: blueprint e_x=[kappa(x):kappa(y)]
(blueprint: lem-a1-condensed-finite-etale-stalk-cycles). -/
def residueDegree (g₀ : X₀ ⟶ Y₀) (y : Y₀.left) (x : ModelPoints D g₀ y) : ℕ :=
  letI := ((Y₀.left.residueFieldCongr x.property.symm).hom ≫
    g₀.left.residueFieldMap x.val).hom.toAlgebra
  Module.finrank (Y₀.left.residueField y) (X₀.left.residueField x.val)

/-- The restriction arrow, obtained from the actual pullback/direct-image counit.
Source: blueprint pi_z; Stacks 03QP
(blueprint: lem-a1-condensed-finite-etale-stalk-cycles). -/
def restriction (g₀ : X₀ ⟶ Y₀) (M : Modules l (D.geometricFiber X₀).left)
    (ybar : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (z : CondensedRing.FibrePoints (geometricMap D g₀) ybar) :
    fibre l D (directImage D l g₀ M) ybar ⟶ fibre l D M z.val :=
  (CondensedRing.pointSections l D.k).map
    (CondensedRing.stalkLowerStarProj (Profinite.padicAlgClRingObj l) z.property M)

end WeilConjectures.CondensedFiniteEtale

namespace WeilConjectures.CondensedFiniteEtale

/-- The existing coefficient-heart stratification criterion, using its proved local
finite-presentation argument directly. This avoids carrying the unused closure and
abelian-category clauses through the fibre-comparison proof. -/
private theorem lisseStratification_iff_constructible (T : Scheme.{u}) [IsNoetherian T]
    (M : Modules l T) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T M ↔
      ∃ S : T.FiniteLocallyClosedStratification,
        ∀ a : Fin S.n, IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (S.immersion a)).obj M) := by
  refine heart_stratified_lisse (Profinite.padicAlgClRingObj l) ?_ T M
  intro Y _ N
  exact ⟨heart_lfp_of_lisse (Profinite.padicAlgClRingObj l),
    condensedQbar_lfp_locally_free l Y N⟩

end WeilConjectures.CondensedFiniteEtale
