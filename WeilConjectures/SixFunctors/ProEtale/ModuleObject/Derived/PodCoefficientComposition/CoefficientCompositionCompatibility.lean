/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedPoincareDualityConventions.PoincareDualityConventionsCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.Data.Finset.Max
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenFiltrationSuccessor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.ConstructibleSheaf.Devissage
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
public import WeilConjectures.AlgebraicGeometry.FiniteCondensedCtfEquivalence
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteScalarConstantModels
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
public import Mathlib.RingTheory.Finiteness.Projective
public import WeilConjectures.AlgebraicGeometry.EtaleLocallyConstantPerfectComplex
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartOrderedRefinement
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.EtaleDomainPullbackCalculus
public import WeilConjectures.AlgebraicGeometry.EtaleLisseCtfPerfectLocalModel
public import WeilConjectures.AlgebraicGeometry.RefinementPreservesFiniteLisse
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.OpenClosed.Complex
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartGeneration
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedSiteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction
public import WeilConjectures.CategoryTheory.Monoidal.Closed.EvaluationBidualComparisonTransport
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BidualityCoefficients
public import WeilConjectures.CategoryTheory.ObjectProperty.Duality
public import WeilConjectures.CategoryTheory.Monoidal.Closed.InvertibleDualizing
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal

/-! # Composition of coefficient transport for strict duality data

Source: latest blueprint, prop-pod-dual-tate-data-compatibility, proof Step 5,
with the constructions of Steps 1--4 (blueprint: lem-pod-reindexing-composition-compatibility).

Every comparison below is constructed from scalar adjunctions, balanced tensor maps,
root-tower Tate lines and the normalized smooth orientation. Tensors are ordinary
uncompleted derived tensors. Frobenius is the semilinear scheme automorphism.

## Main definitions and statement

* `Compatible`: the complete equations for the canonical comparison arrows.
* `coefficientCompositionCompatibility`: the one-step/two-step transport statement.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.PodCoefficientComposition

/-- Use the bundled commutativity proof without changing the ring object.
Source: coefficient conventions (blueprint: lem-pod-reindexing-composition-compatibility). -/
instance ringComm (R : ScalarSixRing.{u}) : IsCommMonObj R.X := R.comm

/-- Commutativity of the existing pulled-back coefficient object.
Source: coefficient conventions (blueprint: lem-pod-reindexing-composition-compatibility). -/
instance pulledRingComm (R : ScalarSixRing.{u}) (X : Scheme.{u}) :
    IsCommMonObj (condensedRingObj R.X X) :=
  ProEtale.isCommMonObj_condensedRingObj R.X X


/-- Ordinary extension along the already recorded pulled-back ring homomorphism.
Source: balanced scalar tensors in Step 3
(blueprint: lem-pod-reindexing-composition-compatibility). -/
abbrev ordinaryChange {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (X : Scheme.{u}) :=
  Mod.extendScalars (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)

/-- The existing balanced-tensor monoidal structure on ordinary scalar extension.
Source: Step 3 (blueprint: lem-pod-reindexing-composition-compatibility). -/
instance ordinaryChangeMonoidal {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (X : Scheme.{u}) : (ordinaryChange a X).Monoidal :=
  Mod.extendScalarsMonoidal (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)

/-- Vary the coefficient extension and positive level, retaining the fixed geometry.
Source: the three coefficient stages in Step 5
(blueprint: lem-pod-reindexing-composition-compatibility). -/
def setting (P : WeilConjectures.CondensedPoincareDualityConventions.{u})
    (E : PadicAlgCl.FiniteIntermediateField P.ell) (n : ℕ) (hn : 1 ≤ n) :
    WeilConjectures.CondensedPoincareDualityConventions.{u} :=
  { P with extension := E, level := n, level_pos := hn }

/-- The ordinary positive-line map, fixed on the root factor and balanced scalars.
Zero uses the unit comparison; successor uses tensor and the first-line associator.
Source: Step 3, the formula on root sections
(blueprint: lem-pod-reindexing-composition-compatibility). -/
def positiveLine (ell : ℕ) [Fact ell.Prime] {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell) (X : Scheme.{u}) :
    (n : ℕ) →
      (ordinaryChange a X).obj (c.line ell X n) ≅
        c'.line ell X n
  | 0 =>
      letI := ordinaryChangeMonoidal a X
      (Functor.Monoidal.εIso (ordinaryChange a X)).symm
  | n + 1 =>
      letI := ordinaryChangeMonoidal a X
      (Functor.Monoidal.μIso (ordinaryChange a X)
        (c.line ell X n) (c.firstLine ell X)).symm ≪≫
      tensorIso (positiveLine ell a ha X n) (scalarFirst ell a ha X)

/-- The signed ordinary line map. Negative powers use the evaluation transpose,
unit comparison and inverse positive-line comparison in the contravariant slot.
Source: Step 3, negative Tate powers
(blueprint: lem-pod-reindexing-composition-compatibility). -/
def signedLine (ell : ℕ) [Fact ell.Prime] {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell) (X : Scheme.{u}) :
    (r : ℤ) →
      (ordinaryChange a X).obj
        (StrictWeilCondensed.presentationLine ell c X r) ⟶
      StrictWeilCondensed.presentationLine ell c' X r
  | .ofNat n => (positiveLine ell a ha X n).hom
  | .negSucc n =>
      letI := ordinaryChangeMonoidal a X
      (Functor.LaxMonoidal.ihomComparison
        (ordinaryChange a X) (c.line ell X (n + 1))).natTrans.app
          (𝟙_ _) ≫
      (ihom ((ordinaryChange a X).obj
        (c.line ell X (n + 1)))).map
          (Functor.Monoidal.εIso (ordinaryChange a X)).inv ≫
      (MonoidalClosed.pre (positiveLine ell a ha X (n + 1)).inv).app (𝟙_ _)

/-- Localize an ordinary scalar arrow by the derived scalar/restriction adjunction.
This is the same construction as scalarLineZero, for any ordinary module arrow.
Source: Step 3, ordinary lines compute the derived scalar map
(blueprint: lem-pod-reindexing-composition-compatibility). -/
def deriveLine {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (X : Scheme.{u})
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))
    (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ'.X X))
    (f : (ordinaryChange a X).obj M ⟶ N) :
    (scalarSixChange a X).obj ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (DerivedCategory.singleFunctor _ 0).obj N :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).homEquiv
    ((DerivedCategory.singleFunctor _ 0).obj M)
    ((DerivedCategory.singleFunctor _ 0).obj N) |>.symm <|
    (DerivedCategory.singleFunctor _ 0).map
      ((Mod.extendRestrictAdjunction
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).homEquiv _ _ f) ≫
    ((Mod.comap (C := Sheaf (ProEt.topology X) Ab.{u + 1})
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).mapDerivedCategorySingleFunctor
        0).inv.app N

/-- The actual signed Tate-line map, using the recorded identification of signed lines.
Source: Step 3, all integer twists
(blueprint: lem-pod-reindexing-composition-compatibility). -/
def tateMap (ell : ℕ) [Fact ell.Prime] {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell) (X : Scheme.{u}) (r : ℤ) :
    (scalarSixChange a X).obj (StrictWeilCondensed.derivedTateLine ell c X r) ⟶
      StrictWeilCondensed.derivedTateLine ell c' X r :=
  (scalarSixChange a X).map ((DerivedCategory.singleFunctor _ 0).map
    (StrictWeilCondensed.tateLine_identification ell c X r).hom) ≫
  deriveLine a X _ _ (signedLine ell a ha X r) ≫
    (DerivedCategory.singleFunctor _ 0).map
      (StrictWeilCondensed.tateLine_identification ell c' X r).inv


/-- Tensor the dual and the signed Tate comparisons, retaining the scalar tensorator.
Source: Step 3 (blueprint: lem-pod-reindexing-composition-compatibility). -/
def twistedMap (ell : ℕ) [Fact ell.Prime] {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell)
    (X : Scheme.{u}) (K : c.derived ell X) (r : ℤ) :=
  (scalarSixTensorIso a X (StrictWeilCondensed.dual (c.obj ell) K)
    (StrictWeilCondensed.derivedTateLine ell c X r)).hom ≫
      (dualMap a X K ⊗ₘ tateMap ell a ha X r)

/-- The Tate-line comparison intertwines the root-normalized geometric Frobenius datum.
Source: Step 3, tau_r including negative and zero r
(blueprint: lem-pod-reindexing-composition-compatibility). -/
def TateSquare (ell : ℕ) [Fact ell.Prime] {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell)
    {X : Scheme.{u}} (g : X ≅ X)
    [∀ x : X, Invertible (ell : X.residueField x)] (r : ℤ) : Prop :=
  (StrictWeilCondensed.action (c'.obj ell) g).map (tateMap ell a ha X r) ≫
      (StrictWeilCondensed.tateDatum ell c' g r).hom =
    (datum a g _ (StrictWeilCondensed.tateDatum ell c g r)).hom ≫ tateMap ell a ha X r

/-- The analogous square for the tensor of the contragredient datum and tau_r.
Source: Step 3 (blueprint: lem-pod-reindexing-composition-compatibility). -/
def TwistedSquare (ell : ℕ) [Fact ell.Prime] {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell)
    {X : Scheme.{u}} (g : X ≅ X)
    [∀ x : X, Invertible (ell : X.residueField x)] (K : c.derived ell X)
    (phi : (StrictWeilCondensed.action (c.obj ell) g).obj K ≅ K) (r : ℤ) : Prop :=
  (StrictWeilCondensed.action (c'.obj ell) g).map (twistedMap ell a ha X K r) ≫
      (StrictWeilCondensed.twistedDualDatum ell c' g ((scalarSixChange a X).obj K)
        (datum a g K phi) r).hom =
    (datum a g _ (StrictWeilCondensed.twistedDualDatum ell c g K phi r)).hom ≫
      twistedMap ell a ha X K r

set_option maxHeartbeats 2000000 in
-- The full tower formula elaborates three coefficient stages and their native module instances.
/-- One-step and two-step coefficient transport of strict contragredient, evaluation,
Tate, purity-duality and evaluation-biduality data agree under the canonical scalar tower.
The three stages can use different finite coefficient extensions and positive levels.
The scalar-map predicate includes small finite carriers in every ambient universe
and isomorphic presentation changes. The existential equalities ha, hb, hab certify
the fixed integral coefficient maps;
all morphisms in the conclusion have the explicit constructions above.

Source: latest blueprint prop-pod-dual-tate-data-compatibility, proof Step 5, with
Steps 1--4 fixing its maps (blueprint: lem-pod-reindexing-composition-compatibility).

Proof in words:
1. Use det-prop-scalar-six-pullback, lem-sfb-ringed-derived-monoidal-comparisons,
sk-def-sfb-coefficient-change and sk-prop-scalar-six.
Pullback/coefficient comparison is the normalized ringed-topos mate, also for the
semilinear geometric Frobenius. The coefficient square commutes because coefficients
are pulled from the point. ScalarCompatible gives ha and hb for the listed scalar
maps; associativity gives hab. The finite and integralFinite constructors use
Type-0 carriers without equating the ambient universe with zero; presentation
isomorphisms are covered by the iso constructor. Its tower square identifies the
one-step datum with the
successive data under the scalar associator.
2. Use det-prop-scalar-six-tensor-hom, sk-def-sf-weil-complexes and thm-sf-dual-perfect.
The scalar Hom comparison is the transpose of scalar extension of evaluation.
Apply this identity successively for a and b. Monoidality of the scalar associator
identifies the evaluations; uniqueness of transpose identifies the dual comparisons.
Substitute them into the three-arrow contragredient formula, using naturality of
phi inverse and the scalar unit comparison. This proves the three dual squares,
the dual tower equation and the evaluation equations.
3. Use sk-def-sp-tate-twist and lem-sp-invertible-tensor-scalar-extension.
The first Tate-line map acts on the scalar factor and leaves the root factor fixed.
Thus two changes multiply balanced scalars exactly as their composite and commute
with root pullback. Tensor recursion proves the positive cases, the scalar unitor
the zero case, and evaluation transpose the negative cases. Localization computes
ordinary derived scalar extension because these lines are locally free of rank one.
Tensoring with step 2 proves all twisted squares and their tower equations.
4. Use thm-sf-dual-perfect, thm-pur-weil-equivariance-of-purity-and-trace,
lem-fix-weil-operations, sk-thm-pd-verdier-duality and det-prop-scalar-six-exceptional.
Smooth purity identifies the normalized exceptional unit with the shifted Tate
line. Its scalar counit square identifies omegaMap with the specified exceptional
comparison. Apply the orientation and twist-interchange formula to step 2 and the
shifted line calculation of step 3. This gives the purity squares and their composite.
Finally delta is the transpose of evaluation after Koszul symmetry. Transpose the
same scalar evaluation equation twice to obtain the biduality squares. Hom and
exceptional tower coherence identify the two-step square with the one-step square.
-/
theorem coefficientCompositionCompatibility
    (P : WeilConjectures.CondensedPoincareDualityConventions.{u})
    (E₁ E₂ : PadicAlgCl.FiniteIntermediateField P.ell)
    (n₁ n₂ : ℕ) (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    (s₀ s₁ s₂ : WeilConjectures.PoincareCoefficient) :
    Compatible P E₁ E₂ n₁ n₂ hn₁ hn₂ s₀ s₁ s₂ := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.PodCoefficientComposition
