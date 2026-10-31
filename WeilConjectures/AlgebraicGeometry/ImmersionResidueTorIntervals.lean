/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ResidueTorAmplitudeTest
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ComparisonTorInterval
import WeilConjectures.AlgebraicGeometry.SfClosedPartitionModuleTest
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackExact
import WeilConjectures.AlgebraicGeometry.FiniteImmersionConstructibilityInterval
import WeilConjectures.AlgebraicGeometry.ProEtaleResidueTorTest
import WeilConjectures.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
import WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Sites.RegularEpi
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.Mathlib.CategoryTheory.NatIso
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import WeilConjectures.AlgebraicGeometry.ProEtaleRingedOpenClosed
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.SixFunctors.ProEtaleClosedTensorProjection
import WeilConjectures.AlgebraicGeometry.OrdinaryDerivedOpenClosedAdjunctions
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingMap
import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit

/-! # Residue tensor intervals for immersion operations

Source: main-20261015, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-localization-all-stages.proof.md, Residue criterion and (3 prime)
(blueprint: lem-sf-immersion-residue-tor-intervals).

All tensors are ordinary unbounded derived tensors. The maps below specialize the
published monoidal comparison and adjunction-mate projection to a constant module.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

section Coefficients

variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A]

/-- The canonical derived identification of the pullback of a constant module.
Source: blueprint, Residue criterion; constant-coefficient identifications
(blueprint: lem-sf-immersion-residue-tor-intervals). -/
@[irreducible] def immersionResidueConstantPullbackIso {Y X : Scheme.{u}} (f : Y ⟶ X) (M : A) :=
  (singleFunctorCompLeftDerivedUpperStarIso A f).app
    ((constantSheaf (Scheme.ProEt.topology X) A).obj M) ≪≫
    (_root_.DerivedCategory.singleFunctor
      (Sheaf (Scheme.ProEt.topology Y) A) 0).mapIso
      ((constantSheafCompUpperStarIso A f).app M)

/-- The specified monoidal pullback comparison, followed by the constant-module
identification. It applies to unbounded objects and any constant module.
Source: blueprint, Residue criterion
(blueprint: lem-sf-immersion-residue-tor-intervals). -/
@[irreducible] def immersionResidueTensorPullbackIso {Y X : Scheme.{u}} (f : Y ⟶ X) (M : A)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  leftDerivedUpperStarTensorIso A f K
    ((_root_.DerivedCategory.singleFunctor
      (Sheaf (Scheme.ProEt.topology X) A) 0).obj
        ((constantSheaf (Scheme.ProEt.topology X) A).obj M)) ≪≫
    ((derivedTensor A Y).obj
      ((upperStar A f).leftDerivedFunctor.obj K)).mapIso
        (immersionResidueConstantPullbackIso A f M)

/-- The canonical projection map, with target identified using the actual pullback
of the constant module. This is the adjunction mate, not a chosen isomorphism.
Source: blueprint, (3 prime) for closed pushforward
(blueprint: lem-sf-immersion-residue-tor-intervals). -/
@[irreducible] def immersionResidueProjectionMap {Z X : Scheme.{u}} (i : Z ⟶ X) (M : A)
    (P : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) :=
  ((rightDerivedLowerStarProjectionMap A i).app P).app
    ((_root_.DerivedCategory.singleFunctor
      (Sheaf (Scheme.ProEt.topology X) A) 0).obj
        ((constantSheaf (Scheme.ProEt.topology X) A).obj M)) ≫
    (lowerStar A i).rightDerivedFunctor.map
      (((derivedTensor A Z).obj P).map
        (immersionResidueConstantPullbackIso A i M).hom)

/-- The canonical monoidal etale/pro-etale comparison at a constant module, on the
unbounded categories. Source: blueprint, Residue criterion
(blueprint: lem-sf-immersion-residue-tor-intervals). -/
@[irreducible] def immersionResidueSiteComparisonIso
    (T : Scheme.{u}) [(comparisonUpperStar A T).PreservesFlat] (M : A)
    (C : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)) :=
  (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    A C).app
    ((_root_.DerivedCategory.singleFunctor
      (Sheaf T.smallEtaleTopology A) 0).obj
        ((constantSheaf T.smallEtaleTopology A).obj M)) ≪≫
    ((derivedTensor A T).obj
      ((comparisonUpperStar A T).mapDerivedCategory.obj C)).mapIso
        (((comparisonUpperStar A T).mapDerivedCategorySingleFunctor 0).app
          ((constantSheaf T.smallEtaleTopology A).obj M) ≪≫
          (_root_.DerivedCategory.singleFunctor
            (Sheaf (Scheme.ProEt.topology T) A) 0).mapIso
            (((((constantSheafAdj T.smallEtaleTopology A
              (Scheme.Etale.isTerminalMkId T)).comp (comparisonAdjunction A T)).ofNatIsoRight
                ((Scheme.toProEt T).sheafPushforwardContinuousCompSheafSectionsObjIso A
                  T.smallEtaleTopology (Scheme.ProEt.topology T)
                  (Opposite.op (Scheme.Etale.mk (𝟙 T))))).leftAdjointUniq
                    (constantSheafAdj (Scheme.ProEt.topology T) A
                      (Scheme.ProEt.isTerminalMkId T))).app M))

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ V W, FunLike (FA V W) (CA V) (CA W)] [ConcreteCategory.{u + 1} A FA]

/-- The pullback clauses, for one of the two specified immersions: bounded
constructibility, preservation of a given Tor interval, and preservation of the
cohomological interval of the residue tensor. The canonical comparison is
`immersionResidueTensorPullbackIso`.
Source: blueprint, (3 prime) for inverse images
(blueprint: lem-sf-immersion-residue-tor-intervals). -/
def ImmersionResiduePullbackAssertion (M : A) {X Y : Scheme.{u}} (f : Y ⟶ X) (a b : ℤ) : Prop :=
  ∀ K : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) A),
      DerivedCategory.boundedConstructible A X K →
        DerivedCategory.boundedConstructible A Y
          ((upperStar A f).leftDerivedFunctor.obj K) ∧
        (DerivedCategory.torAmplitudeIn A X a b K →
          DerivedCategory.torAmplitudeIn A Y a b
            ((upperStar A f).leftDerivedFunctor.obj K)) ∧
        (_root_.DerivedCategory.homologyConcentratedIn a b
          (((derivedTensor A X).obj K).obj
            ((_root_.DerivedCategory.singleFunctor
              (Sheaf (Scheme.ProEt.topology X) A) 0).obj
                ((constantSheaf (Scheme.ProEt.topology X) A).obj M))) →
          _root_.DerivedCategory.homologyConcentratedIn a b
            (((derivedTensor A Y).obj
              ((upperStar A f).leftDerivedFunctor.obj K)).obj
                ((_root_.DerivedCategory.singleFunctor
                  (Sheaf (Scheme.ProEt.topology Y) A) 0).obj
                    ((constantSheaf (Scheme.ProEt.topology Y) A).obj M)))
)

/-- The immersion and comparison assertions at one specified constant module.
The theorem below specializes this package only to the actual residue quotient.
Source: blueprint, Residue criterion and (3 prime)
(blueprint: lem-sf-immersion-residue-tor-intervals). -/
def ImmersionResidueTorAssertion (M : A) {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) : Prop :=
  ∀ (a b : ℤ), a ≤ b →
    ImmersionResiduePullbackAssertion A M i a b ∧
    ImmersionResiduePullbackAssertion A M j a b ∧
    (∀ P : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology Z) A),
      DerivedCategory.boundedConstructible A Z P →
        DerivedCategory.boundedConstructible A X
          ((lowerStar A i).rightDerivedFunctor.obj P) ∧
        (DerivedCategory.torAmplitudeIn A Z a b P →
          DerivedCategory.torAmplitudeIn A X a b
            ((lowerStar A i).rightDerivedFunctor.obj P)) ∧
        IsIso (immersionResidueProjectionMap A i M P)) ∧
    ∀ (T : Scheme.{u}), T = X ∨ T = Z ∨ T = U →
      ∀ C : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A),
        Etale.DerivedCategory.boundedConstructible A T C →
        ((_root_.DerivedCategory.homologyConcentratedIn a b
          (((Etale.derivedTensor A T).obj C).obj
            ((_root_.DerivedCategory.singleFunctor
              (Sheaf T.smallEtaleTopology A) 0).obj
                ((constantSheaf T.smallEtaleTopology A).obj M))) ↔
          _root_.DerivedCategory.homologyConcentratedIn a b
            (((derivedTensor A T).obj
              ((comparisonUpperStar A T).mapDerivedCategory.obj C)).obj
                ((_root_.DerivedCategory.singleFunctor
                  (Sheaf (Scheme.ProEt.topology T) A) 0).obj
                    ((constantSheaf (Scheme.ProEt.topology T) A).obj M)))) ∧
        (Etale.DerivedCategory.torAmplitudeIn A T a b C ↔
          DerivedCategory.torAmplitudeIn A T a b
            ((comparisonUpperStar A T).mapDerivedCategory.obj C))
)

end Coefficients

/-- The preceding assertion specialized to module sheaves over a finite ring.
Finiteness supplies the existing Noetherian flat-pullback instance.
Source: blueprint, Residue criterion and (3 prime)
(blueprint: lem-sf-immersion-residue-tor-intervals). -/
def immersionResidueFiniteAssertion (A : Type (u + 1)) [CommRing A] [Finite A]
    (M : ModuleCat.{u + 1} A) {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) : Prop :=
  ImmersionResidueTorAssertion (ModuleCat.{u + 1} A) M i j

/-- Finite immersion operations preserve bounded constructibility and each Tor interval;
the canonical residue projection is invertible, and comparison preserves and detects
residue cohomological intervals and Tor intervals. No perfectness of the residue is used.
Source: main-20261015, localization proof, Residue criterion and (3 prime)
(blueprint: lem-sf-immersion-residue-tor-intervals).

Proof (the seven DAG steps):
1. Finite type over a field makes X Noetherian, so its complementary open is
quasi-compact (lem-weil-pbc-finite-type-over-noetherian and
lem-sf-closed-partition-module-test). Apply
lem-sf-finite-immersion-constructibility-interval to obtain constructibility.
2. Immersion inverse images are exact by
lem-weil-pbc-proetale-immersion-limit-preservation and the constant ring comparison;
closed direct image is exact by lem-weil-pbc-proetale-ringed-open-closed.
The exact-functor derived comparison and cohomology comparison therefore preserve
intervals on unbounded complexes. Use lem-sf-comparison-pullback-exact for nu.
3. The unbounded monoidal pullback comparison identifies the pullback of the residue
tensor with tensor of the pullback, since the constant-module identification respects
the quotient action. No lower bound on the tensor is required.
4. The closed tensor projection lemma puts i_*P tensor M in the image of i_*.
The closed counit and triangle identity make its unit invertible. The projection map
is that unit, followed by the monoidal comparison and the tensor of the counit;
all factors are invertible. Take M to be the constant residue module.
5. Apply lem-sf-proetale-residue-tor-test on X and then on Z and U: the unchanged
residue cohomological interval is exactly the unchanged Tor interval.
6. For an arbitrary degree-zero test sheaf N, i^*N is again degree zero.
The projection isomorphism and exactness of i_* preserve the interval of
P tensor i^*N; this is Tor amplitude of i_*P tested against every N.
7. For each degree r, exact comparison commutes with H^r even on an unbounded-below
residue tensor. Apply the bounded-below site comparison to H^r[0] to reflect its
vanishing. Finally lem-exc-comparison-tor-interval gives preservation and reflection
of Tor amplitude for the original bounded constructible etale complex. -/
theorem immersion_residue_tor_intervals
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : k))
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) {X Z U : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ) :
    @immersionResidueFiniteAssertion
      (Padic.coefficientExtensionRing l E n) _
      (Padic.finite_coefficientExtensionRing l E n hn)
      (Padic.coefficientExtensionResidueModule l E n) X Z U i j := by
  sorry

end AlgebraicGeometry.ProEtale
