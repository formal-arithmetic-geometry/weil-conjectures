/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.Paper.IntegralAmbientDirectImageEncoding
public import Sheaf.Paper.CompletedCondensedCoefficients
public import Sheaf.Paper.CartesianCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.ContinuousCoefficientModuleEncoding
public import Sheaf.Paper.CompletedDirectImageLimits
public import Sheaf.Paper.RingedEtaleOriginWitness
public import Sheaf.CategoryTheory.ConstantScalarRestrictionTensor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Sheaf.AlgebraicGeometry.UnboundedDirectImageComparisonMap
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Sheaf.Paper.CoefficientSystemDerivedComparison
import Sheaf.Paper.CompletedCoefficientPushforwardComparison
import Sheaf.CategoryTheory.DiagramRingRestrictionPushforward
import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.AugmentedDiagramProjectionMate
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.Paper.ReductionPullbackDerivedTower
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Sheaf.Paper.PerfectProjectionFormula
public import Sheaf.AlgebraicGeometry.UnboundedDirectImageBoundedBelow

/-! # Ordinary integral direct image and its finite reduction tower

Source: Bhatt--Scholze, Lemmas 6.5.9(2),(3) and 5.4.3
(blueprint: lem-sfb-integral-ambient-tower-comparison).

The coefficient comparisons preserve the specified quotient maps. All derived
categories are ordinary ambient categories. The strict tower map and its augmentation
are the normalized adic projection mate, before any derived inverse limit is taken.
-/

@[expose] public noncomputable section
set_option autoImplicit false

set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.hasDerived
universe u
open scoped CategoryTheory.Obj
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme.IntegralAmbientTower
attribute [-instance] ConstantScalarRestriction.fixedAbelian
attribute [-instance] ConstantScalarRestriction.fixedPreadditive
attribute [-instance] ConstantScalarRestriction.fixedZeroMorphisms


variable (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)

/-- Finiteness, l-power annihilation and the normalized finite free resolution.
Source: Bhatt--Scholze, Lemma 6.5.9(3)
(blueprint: lem-sfb-integral-ambient-tower-comparison).
Proof: l=πa implies l^(n+1)=π^(n+1)a^(n+1); it annihilates the quotient.
The cone of multiplication by π^(n+1) has only the two displayed free terms.
Its degree -1 cohomology is zero since the valuation ring is a domain, and its
zeroth cohomology is precisely the quotient. Augment by the quotient map, giving
the normalization on the degree-zero inclusion. This is the resolution used in
the perfect projection formula of lemma-weil-pbc-perfect-projection-formula. -/
theorem finiteResolution (π : PadicAlgCl.integers l E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
    (n : ℕ) :
    (∀ x : integers.{u} l E ⧸ (Ideal.span {ULift.up π}) ^ (n + 1), l ^ (n + 1) • x = 0) ∧
      ∃ ε : resolution.{u} l E π n ⟶ quotientComplex.{u} l E π n,
        QuasiIso ε ∧
        (resolution.{u} l E π n).IsStrictlyGE (-1) ∧
        (resolution.{u} l E π n).IsStrictlyLE 0 ∧
        HasFiniteFreeTerms (resolution.{u} l E π n) := by
  sorry

/-- The canonical coefficient models exist, without hypotheses on the scheme.
Source: Bhatt--Scholze, Section 6.5; Stacks 09BT
(blueprint: lem-sfb-integral-ambient-tower-comparison).
Proof: use sk-prop-sfb-qlbar-colimit-x on the actual profinite quotient tower.
Finite continuous coefficients identify with constants by their local constant
sections. Transport ULift through the quotient by the class-of-a map; it preserves
all transition maps. The inverse-limit universal property gives the completed
comparison and its projection equation. Reconstructing section rings preserves
these identities and the pointwise scalar formula. Uniqueness follows locally
from constant sections, and then from the jointly monic limit projections. -/
theorem coefficientModel_exists (π : PadicAlgCl.integers l E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
    (T : Scheme.{u}) : Nonempty (CoefficientModel l E π hπ T) := by
  sorry

/-- The canonical encodings exist for every morphism and every positive finite level.
Source: Bhatt--Scholze, Section 6.5; Stacks 0D6E
(blueprint: lem-sfb-integral-ambient-tower-comparison).
Proof: the sectionModuleEquivalence is identity on the underlying abelian sheaf,
and scalar transport uses the projection-normalized ring comparisons. The
coefficient inverse-image identity of lem-weil-pbc-profinite-coefficient-inverse-image
therefore makes the ordinary direct-image actions equal. The identity section maps
give the ordinary comparisons. Exact equivalences preserve K-injectives; uniqueness
of total right-derived functors gives the derived comparisons with the displayed
unit normalization. Apply the same argument to each constant finite quotient,
using its constants-to-functions map. No scheme hypothesis is used here. -/
theorem encodings (π : PadicAlgCl.integers l E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (CX : CoefficientModel l E π hπ X) (CY : CoefficientModel l E π hπ Y) :
    Nonempty (AmbientEncoding l E f CX CY) ∧
      ∀ n : ℕ, Nonempty (FinitePushEncoding l E (π := π) (hπ := hπ) f n) := by
  sorry

/-- Roos completeness and invertibility of the specified strict quotient completion
unit coincide; the actual quotient-unit legs are retained throughout.
Source: Bhatt--Scholze, Definition 3.5.2; Stacks 08TC and 099N
(blueprint: lem-sfb-integral-ambient-tower-comparison).
Proof: a Roos triangle gives an isomorphism with the derived quotient limit.
That limit is intrinsically complete by the Koszul completion reflector; hence
so is the input. Koszul reconstruction then identifies its actual intrinsic unit
with the specified quotient unit and makes it invertible. Conversely transport
the canonical strict-limit Roos triangle along that unit. This is precisely the
argument in lem-pur-completed-coefficient-pushforward-comparison, Steps 6--7;
it does not select an arbitrary lifting of the Roos product arrow. -/
theorem complete_iff (π : PadicAlgCl.integers l E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
    (T : Scheme.{u}) (K : (datum.{u} l E π hπ).derived T) :
    (datum.{u} l E π hπ).quotientRoosComplete T K ↔
      (datum.{u} l E π hπ).TowerComplete T K := by
  sorry

/-- The ordinary direct image preserves completeness and compares to one strict
finite reduction tower, with its coefficient-linear evaluations and augmentation.
Source: Bhatt--Scholze, Lemma 6.5.9(2),(3); Stacks 0A07 and 099N
(blueprint: lem-sfb-integral-ambient-tower-comparison).
Proof: (1) Arithmetic and finiteResolution give the Noetherian adic hypotheses,
finite l-primary quotients and their two-term free resolutions.
(2) coefficientModel_exists identifies the condensed coefficients with the adic
datum, preserving constants and all quotient projections; cartesian coefficients
give the canonical inverse-image isomorphisms. encodings identifies the ordinary
ambient K-injective direct image, with its action, with d.push.
(3) The perfect projection formula and the scalar-change adjunction produce the
actual P_n-linear finiteProjection isomorphisms. Restriction is conservative.
(4) Apply the reduction/pullback comparison to the ambient counit and transpose
under the strict tower adjunction. Its evaluated arrows are precisely those finite
projections; their tensor formulas commute with every quotient transition. This
is d.towerProjection, with evaluation normalized by towerPushReductionEvaluation.
(5) The augmented projection mate identifies its completion composite with direct
image of the original quotient unit followed by the projection-normalized Rlim
comparison. complete_iff converts the Roos input condition to invertibility of
that unit. The strict map and Rlim comparison are isomorphisms, so the ordinary
pushforward unit is invertible. complete_iff on Y gives its Roos completeness.
The final equality asserts the canonical completion map, not a bare isomorphism
to the same object. All of this is unbounded and uses no properness or origin data. -/
theorem comparison (π : PadicAlgCl.integers l E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : (datum.{u} l E π hπ).derived X)
    (hK : (datum.{u} l E π hπ).quotientRoosComplete X K) :
    (datum.{u} l E π hπ).quotientRoosComplete Y (((datum.{u} l E π hπ).push f).obj K) ∧
      (∀ n : ℕ, IsIso ((datum.{u} l E π hπ).finiteProjection f K n)) ∧
      IsIso ((datum.{u} l E π hπ).towerProjection f K) ∧
      (∀ n : ℕ,
        (reductionTowerDerivedEvaluation Y
            (reductionModuleRing Y ((datum.{u} l E π hπ).completedRing Y)) n).map
              ((datum.{u} l E π hπ).towerProjection f K) ≫
            (datum.{u} l E π hπ).towerPushReductionEvaluation f K n =
          (completedReductionEvaluation Y (datum.{u} l E π hπ) n).app
              (((datum.{u} l E π hπ).push f).obj K) ≫
            (reductionDerivedRestrict Y ((datum.{u} l E π hπ).projection Y n)).map
              ((datum.{u} l E π hπ).finiteProjection f K n)) ∧
      IsIso ((datum.{u} l E π hπ).completionUnit Y (((datum.{u} l E π hπ).push f).obj K) ≫
        (completedRlim Y ((datum.{u} l E π hπ).completedRing Y)).map
            ((datum.{u} l E π hπ).towerProjection f K)) ∧
      (datum.{u} l E π hπ).completionUnit Y (((datum.{u} l E π hπ).push f).obj K) ≫
          (completedRlim Y ((datum.{u} l E π hπ).completedRing Y)).map
            ((datum.{u} l E π hπ).towerProjection f K) =
        ((datum.{u} l E π hπ).push f).map ((datum.{u} l E π hπ).completionUnit X K) ≫
          ((datum.{u} l E π hπ).directImageRlimIso f).hom.app
            ((completedReductionTower X (datum.{u} l E π hπ)).obj K) := by
  sorry



/-- The recorded comparison inverse image in its fixed-scalar localization.
This is a typed specialization of the existing exact derived functor.
Source: Bhatt--Scholze, Lemma 5.4.3; Stacks 09A6
(blueprint: lem-sfb-integral-ambient-tower-comparison). -/
def etalePullback (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    DerivedCategory.{u + 1} (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory.{u + 1} (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory

/-- The recorded total direct image in its fixed-scalar localization.
This caches its actual ambient category and imposes no completion.
Source: Bhatt--Scholze, Lemma 5.4.3; Stacks 09A6
(blueprint: lem-sfb-integral-ambient-tower-comparison). -/
def proEtalePush (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.{u + 1} (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory.{u + 1} (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)) :=
  (ProEtale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor

/-- The inverse of the actual bounded-below etale/pro-etale direct-image mate.
Only the proof of its invertibility comes from the published bounded-below theorem;
the arrow is the inverse of that exact mate, not an independently chosen comparison.
Source: Bhatt--Scholze, Lemma 5.4.3; Stacks 09A6
(blueprint: lem-sfb-integral-ambient-tower-comparison). -/
def etaleComparisonInverse (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (b : ℤ) [L.IsGE b] :
    (Functor.rightDerivedFunctor.{u + 2, u + 2, u + 1, u + 1, u + 1, u + 1}
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) f)).obj
        ((Functor.mapDerivedCategory.{u + 1, u + 1}
          (comparisonUpperStar (ModuleCat.{u + 1} A) X)).obj L) ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.{u + 1, u + 1}.obj
        ((Functor.rightDerivedFunctor.{u + 2, u + 2, u + 1, u + 1, u + 1, u + 1}
          (Etale.lowerStar (ModuleCat.{u + 1} A) f)).obj L) :=
  inv (I := unboundedDirectImageComparison_boundedBelow A f L b)
    (unboundedDirectImageComparisonMap A f L)

/-- The optional finite-level etale-origin clause, with the actual reduction and
normalized finite pushforward square. All antecedents and isomorphisms are retained.
Source: Bhatt--Scholze, Lemma 5.4.3 and Lemma 6.5.9(3)
(blueprint: lem-sfb-integral-ambient-tower-comparison). -/
def FiniteEtaleOriginComparison {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : d.derived X) : Prop :=
  ∀ (n : ℕ)
    (H : FiniteCoefficientPushEncoding d f n)
    (L : DerivedCategory.Plus.{u + 1} (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1)))))
    (b : ℤ) [L.obj.IsGE b]
    (θ : (@finiteDerivedFixed.{u} X
        (A ⧸ d.ideal ^ (n + 1)) inferInstance
        (d.quotientFinite n)).obj
          ((d.reduction X n).obj K) ≅
      (etalePullback
        (A ⧸ d.ideal ^ (n + 1)) X).obj
          L.obj),
    IsIso ((FiniteCoefficientPushEncoding.comparison d
        (X := X) (Y := Y) (f := f) (n := n) H).hom.app
          ((d.reduction X n).obj K) ≫
        (proEtalePush
          (A ⧸ d.ideal ^ (n + 1)) f).map
            θ.hom ≫
        @etaleComparisonInverse.{u}
          (A ⧸ d.ideal ^ (n + 1)) inferInstance
          (d.quotientFinite n) X Y f inferInstance inferInstance
          L.obj b inferInstance)

/-- The optional etale antecedent gives the canonical finite-level derived isomorphism,
in the same ringed coefficient coordinates as the integral comparison. Its map is the
normalized finite pushforward encoding, followed by direct image of the specified theta,
followed by the inverse of the actual etale/pro-etale comparison mate.
Source: Bhatt--Scholze, Lemma 5.4.3 and Lemma 6.5.9(3); Stacks 09A6
(blueprint: lem-sfb-integral-ambient-tower-comparison).
Proof: the quotient is finite by arithmetic. Regard the given bounded-below antecedent
as an unbounded etale object. Apply lem-sfb-unbounded-direct-image-bounded-below to its
specified lower bound; this makes the canonical comparison mate invertible. Apply the
ordinary total pro-etale direct image to theta, then compose with that inverse.
FinitePushEncoding.comparison transports the source from the actual ringed finite
pushforward and is normalized by the same ordinary section maps and derived units.
The three factors are isomorphisms, so their prescribed composite is invertible
in the derived category, giving the required canonical derived isomorphism.
No compatibility between antecedents at different levels is used. -/
theorem etaleOriginComparison (π : PadicAlgCl.integers l E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : (datum.{u} l E π hπ).derived X) :
    FiniteEtaleOriginComparison (datum.{u} l E π hπ) f K := by
  sorry

end AlgebraicGeometry.Scheme.IntegralAmbientTower
