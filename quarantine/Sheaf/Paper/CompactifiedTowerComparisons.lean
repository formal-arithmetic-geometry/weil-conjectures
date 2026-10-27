/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.AlgebraicGeometry.ProperCoincidenceNormalized
import Sheaf.Paper.CompletedCompactSupportExchange
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.Paper.FiniteCoefficientDirectImage
public import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Paper.EtaleCompactSupportCoefficientChange
public import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Paper.CompletedCoefficientPushforwardComparison
import Sheaf.Paper.CompactificationCompletedRealization
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.Paper.SfCbcCompactSupportCompositionLimit
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.SfIntegralCompactSupportConstructible
import Sheaf.Paper.SfIntegralDirectImageConstructible
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
public import Sheaf.Paper.CompactificationCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
import WeilConjectures.Compactification.CategoryBaseChange
import WeilConjectures.CategoryTheory.StageSystem.Functor
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.CanonicalOriginCompactSupportComposition

/-! # Compactified direct-image towers and their normalized comparisons

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
prop-functor-package.proof.md, clauses (2) and (3)
(blueprint: lem-sf-package-compactified-tower-comparisons).

The declarations separate the witnessed finite domain, the four coefficient stages,
the two actual reduction maps, normalized tower reconstruction, and proper coincidence.
All comparisons are in derived categories; no cohomology-only replacement is made.

## Main statements

* `sfPackageCompactifiedTowerComparisons`: canonical witnessed refinement comparisons.
* `sfPackageCompactifiedTowerNormalizedReduction`: actual finite refinement/composition maps.
* `sfPackageCompactifiedTowerStageCoherence`: unit, associativity and coefficient models.
* `sfPackageCompactifiedTowerFieldPassage`: all enlarged common-stage presentations.
* `sfPackageCompactifiedTowerIntegralReduction` and
  `sfPackageCompactifiedTowerFiniteReduction`: the actual coefficient-change maps.
* `sfPackageCompactifiedTowerEffectivity`: reconstruction by the normalized counit.
* `sfPackageCompactifiedTowerProperTransitions`: proper tower and limit identification.
* `sfPackageCompactifiedTowerFiniteProperExchange` and
  `sfPackageCompactifiedTowerHigherProperExchange`: the specified proper-exchange equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u v w v' w'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open CategoryTheory.SuppliedExchangeProjection
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor

namespace WeilConjectures

/-- Unit and associativity equations for the specified support maps.
The identity support is identified with the identity through the identity-open proper map.
Source: blueprint prop-functor-package, clauses (2)--(3)
(blueprint: lem-sf-package-compactified-tower-comparisons). -/
def SfPackageCompactSupportCoherence
    {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type v}
    [∀ X, Category.{w} (B X)] (S : SixFunctorPushStage D B) : Prop :=
  (∀ (X : SixFunctorSpace D) [IsSeparated X.obj.hom],
    ∃ identity : S.support (𝟙 X) (.ofIsProper (𝟙 X.obj.left)) ≅ 𝟭 (B X),
    (∀ (Y : SixFunctorSpace D) [IsSeparated Y.obj.hom] (f : X ⟶ Y)
      (c : Compactification f.hom.left) (K : B X),
      (S.composition (𝟙 X) f (.ofIsProper (𝟙 X.obj.left)) c c).hom.app K ≫
        (S.support f c).map (identity.hom.app K) = 𝟙 _) ∧
    (∀ (Y : SixFunctorSpace D) [IsSeparated Y.obj.hom] (f : Y ⟶ X)
      (c : Compactification f.hom.left) (K : B Y),
      (S.composition f (𝟙 X) c (.ofIsProper (𝟙 X.obj.left)) c).hom.app K ≫
        identity.hom.app ((S.support f c).obj K) = 𝟙 _)) ∧
  (∀ (X Y Z T : SixFunctorSpace D)
    [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    [IsSeparated Z.obj.hom] [IsSeparated T.obj.hom]
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification h.hom.left) (cfg : Compactification (f ≫ g).hom.left)
    (cgh : Compactification (g ≫ h).hom.left)
    (cfgh : Compactification ((f ≫ g) ≫ h).hom.left)
    (cfgh' : Compactification (f ≫ (g ≫ h)).hom.left) (K : B X),
    HEq ((S.composition (f ≫ g) h cfg ch cfgh).hom.app K ≫
      (S.support h ch).map ((S.composition f g cf cg cfg).hom.app K))
      ((S.comparison (f ≫ (g ≫ h))
          (cfgh.copy (congrArg (fun a : X ⟶ T ↦ a.hom.left)
            (Category.assoc f g h).symm)) cfgh').hom.app K ≫
        (S.composition f (g ≫ h) cf cgh cfgh').hom.app K ≫
        (S.composition g h cg ch cgh).hom.app ((S.support f cf).obj K)))

/-- Literal action on comparison components in the specified coefficient models.
The functor L is instantiated by rational localization or the common-stage inclusion,
so these equations identify the maps with localized or represented integral maps.
HEq only transports the object equalities of those models; no operation-comparison
record is an argument. Source: blueprint prop-functor-package, clauses (2)--(3)
(blueprint: lem-sf-package-compactified-tower-comparisons). -/
def SfPackageSupportCoefficientLaws
    {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type v}
    [∀ X, Category.{w} (B X)] {B' : SixFunctorSpace D → Type v'}
    [∀ X, Category.{w'} (B' X)]
    (P : SixFunctorPushStage D B) (Q : SixFunctorPushStage D B')
    (L : ∀ X, B X ⥤ B' X) : Prop :=
  (∀ (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) (c d : Compactification f.hom.left) (K : B X),
    HEq ((Q.comparison f c d).hom.app ((L X).obj K))
      ((L Y).map ((P.comparison f c d).hom.app K))) ∧
  (∀ (X Y Z : SixFunctorSpace D)
    [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom] [IsSeparated Z.obj.hom]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : B X),
    HEq ((Q.composition f g cf cg cfg).hom.app ((L X).obj K))
      ((L Z).map ((P.composition f g cf cg cfg).hom.app K))) ∧
  (∀ (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsProper f.hom.left] (K : B X),
    HEq ((Q.properIdentity f).hom.app ((L X).obj K))
      ((L Y).map ((P.properIdentity f).hom.app K)))

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
  (n : ℕ) (hn : 1 ≤ n) (S : SixFunctorOperationDatum D C E n hn)

/-- The coefficient prime is invertible in the geometric base field.
Source: the initial finite-field and coefficient hypotheses of prop-functor-package
(blueprint: lem-sf-package-compactified-tower-comparisons).

Proof: cardinality p^a gives characteristic p on the finite field, hence on its
algebraic closure by injectivity of the field inclusion. Distinct primes p and l
imply that p does not divide l, so the characteristic-p unit criterion applies. -/
theorem sfPackageCoefficientIsUnit : IsUnit (C.l : D.k) := by
  sorry

/-- Reduction of an integral support value by its chosen Roos projection.
The first arrow is the retained equality with the specified support value; the
second is sfCompactSupportChosenReduction, not a coefficient-record component.
Source: blueprint prop-functor-package, integral reduction paragraph
(blueprint: lem-sf-package-compactified-tower-comparisons). -/
def sfPackageIntegralSupportReduction
    (H : SixFunctorHigherOperations D C E)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) (m : ℕ) :=
  (scalarReductionDerivedExtension C.l E Y.obj.left m).map
      ((sfIntegralConstructible C.l E Y.obj.left).ι.map
        (eqToHom ((H.supportConstruction f (sfPackageCoefficientIsUnit D C) c
          ).choose_spec.2.2.1 K))) ≫
    sfCompactSupportChosenReduction C.l D.k (sfPackageCoefficientIsUnit D C) c E K m

/-- The same reduction followed by the specified finite origin coordinates.
It uses the supplied witness and its input isomorphism and chooses no finite map.
Source: blueprint prop-functor-package, integral refinement paragraph
(blueprint: lem-sf-package-compactified-tower-comparisons). -/
def sfPackageIntegralWitnessReduction
    (H : SixFunctorHigherOperations D C E)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [hf : IsSeparated f.hom.left] [hft : LocallyOfFiniteType f.hom.left]
    [hqc : QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) (m : ℕ)
    (O : RefinementFiniteLevelOrigin C.l E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left)
    (w : (sixFunctorFiniteRealization D C E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) X).functor.obj
        (refinementFiniteLevelFixedObject C.l E (m + 1)
          (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left O) ≅
      (scalarReductionDerivedExtension C.l E X.obj.left m).obj K.obj) :=
  sfPackageIntegralSupportReduction D C E H f c K m ≫
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing C.l E (m + 1)) c
      ).map w.inv ≫
    (sfIntrinsicCompactSupportComparison (Padic.coefficientExtensionRing C.l E (m + 1)) c
      ).hom.app (refinementFiniteLevelFixedObject C.l E (m + 1)
        (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left O)

/-- The reduction of a two-letter support word, with both prescribed projection
adjuncts and then the same retained input witness. This is the actual composite
reduction, rather than the component of an abstract coefficient comparison.
Source: blueprint prop-functor-package, normalized word realization paragraph
(blueprint: lem-sf-package-compactified-tower-comparisons). -/
def sfPackageIntegralCompositeWitnessReduction
    (H : SixFunctorHigherOperations D C E)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) (m : ℕ)
    (O : RefinementFiniteLevelOrigin C.l E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left)
    (w : (sixFunctorFiniteRealization D C E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) X).functor.obj
        (refinementFiniteLevelFixedObject C.l E (m + 1)
          (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left O) ≅
      (scalarReductionDerivedExtension C.l E X.obj.left m).obj K.obj) :=
  sfPackageIntegralSupportReduction D C E H g cg ((H.integral.support f cf).obj K) m ≫
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing C.l E (m + 1)) cg
      ).map (sfPackageIntegralWitnessReduction D C E H f cf K m O w) ≫
    (sfIntrinsicCompactSupportComparison (Padic.coefficientExtensionRing C.l E (m + 1)) cg
      ).hom.app ((compactificationOriginCandidate C.l E (m + 1)
        (Nat.succ_le_succ (Nat.zero_le m)) cf).obj O)

/-- Integral refinement and composition reduce to the recorded finite origin maps
through the actual chosen reductions, at every quotient and every origin witness.
The coefficient field is arbitrary, so the theorem also applies to every finite
coefficient-field stage used by the common-stage construction.
Source: blueprint prop-functor-package, clauses (2)--(3)
(blueprint: lem-sf-package-compactified-tower-comparisons).

Proof: realize completed support words by their whole strict quotient towers using
lem-fix-compactification-completed-realization and
lem-sf-cbc-compact-support-composition-limit. On a refinement square use the normalized
proper/open map of lem-cbc-strict-tower-proper-open-calculus. On a compatible
compactification tower use its proper/open compositor and its horizontal and vertical
pasting equations. These are precisely refinementComparisonIsomorphism and the origin
compositor at each finite level. Apply total limit to those strict maps and conjugate
by the word realizations. Their projection normalization identifies the resulting
finite maps with sfCompactSupportChosenReduction. Substitute the retained witness
and its input isomorphism at each occurrence; naturality cancels the intermediate
witness transports. No faithfulness of derived evaluation and no Tor bound is used. -/
theorem sfPackageCompactifiedTowerNormalizedReduction
    (H : SixFunctorHigherOperations D C E)
    (_N : SixFunctorIntegralNormalization D C E H) :
    (∀ (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
      (f : X ⟶ Y) [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left]
      [QuasiCompact f.hom.left] (c d : Compactification f.hom.left) (r : c ⟶ d)
      (K : sfIntegralConstructibleCategory C.l E X.obj.left) (m : ℕ)
      (O : RefinementFiniteLevelOrigin C.l E (m + 1)
        (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left)
      (w : (sixFunctorFiniteRealization D C E (m + 1)
        (Nat.succ_le_succ (Nat.zero_le m)) X).functor.obj
          (refinementFiniteLevelFixedObject C.l E (m + 1)
            (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left O) ≅
        (scalarReductionDerivedExtension C.l E X.obj.left m).obj K.obj),
      (scalarReductionDerivedExtension C.l E Y.obj.left m).map
          ((sfIntegralConstructible C.l E Y.obj.left).ι.map
            ((H.integral.comparison f c d).hom.app K)) ≫
        sfPackageIntegralWitnessReduction D C E H f d K m O w =
      sfPackageIntegralWitnessReduction D C E H f c K m O w ≫
        (sixFunctorFiniteRealization D C E (m + 1)
          (Nat.succ_le_succ (Nat.zero_le m)) Y).functor.map
          (refinementComparisonIsomorphism D.k C.l (sfPackageCoefficientIsUnit D C) E
            (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) f.hom.left r O).hom) ∧
    (∀ (X Y Z : SixFunctorSpace D)
      [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom] [IsSeparated Z.obj.hom]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
      [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
      (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
      (cfg : Compactification (f ≫ g).hom.left)
      (K : sfIntegralConstructibleCategory C.l E X.obj.left) (m : ℕ)
      (O : RefinementFiniteLevelOrigin C.l E (m + 1)
        (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left)
      (w : (sixFunctorFiniteRealization D C E (m + 1)
        (Nat.succ_le_succ (Nat.zero_le m)) X).functor.obj
          (refinementFiniteLevelFixedObject C.l E (m + 1)
            (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left O) ≅
        (scalarReductionDerivedExtension C.l E X.obj.left m).obj K.obj),
      (scalarReductionDerivedExtension C.l E Z.obj.left m).map
          ((sfIntegralConstructible C.l E Z.obj.left).ι.map
            ((H.integral.composition f g cf cg cfg).inv.app K)) ≫
        sfPackageIntegralWitnessReduction D C E H (f ≫ g)
          (hf := inferInstanceAs (IsSeparated (f.hom.left ≫ g.hom.left)))
          (hft := inferInstanceAs (LocallyOfFiniteType (f.hom.left ≫ g.hom.left)))
          (hqc := inferInstanceAs (QuasiCompact (f.hom.left ≫ g.hom.left))) cfg K m O w =
      sfPackageIntegralCompositeWitnessReduction D C E H f g cf cg K m O w ≫
        (sixFunctorFiniteRealization D C E (m + 1)
          (Nat.succ_le_succ (Nat.zero_le m)) Z).functor.map
          (sixFunctorFiniteCompositionComparison C E (m + 1)
            (Nat.succ_le_succ (Nat.zero_le m)) f g cf cg cfg O)) := by
  sorry

/-- Finite witnessed refinement comparisons are the canonical proper/open comparisons;
their common-refinement formula is independent of the refinement and has the triple
cocycle. Every bounded constructible finite input has a retained witness.
Source: blueprint prop-functor-package, clause (2)
(blueprint: lem-sf-package-compactified-tower-comparisons).

Proof: obtain etale origins by lem-weil-pbc-finite-ring-constructible-derived-origin;
lem-sf-comparison-tor-amplitude preserves their Tor interval. Apply
prop-compactification-coherence-detailed to the retained witnesses. Its comparison
is proper composition followed by the inverse proper/open comparison. Its identity
and transitivity equations and prop-compactification-refinement give the displayed
common-refinement formula. Applying it to three targets and cancelling the middle
isomorphism gives the triple cocycle. Empty schemes and identity refinements use
the same canonical units. -/
theorem sfPackageCompactifiedTowerComparisons
    (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left]
    [QuasiCompact f.hom.left] :
    (∀ K : sixFunctorFiniteCategory D C E n hn X,
      ∃ O : RefinementFiniteLevelOrigin C.l E n hn X.obj.left,
        Nonempty ((sixFunctorFiniteRealization D C E n hn X).functor.obj
          (refinementFiniteLevelFixedObject C.l E n hn X.obj.left O) ≅ K.obj)) ∧
    ∃ theta : ∀ (c d : Compactification f.hom.left) (_r : c ⟶ d),
      compactificationOriginCandidate C.l E n hn c ≅
        compactificationOriginCandidate C.l E n hn d,
    (∀ (c d : Compactification f.hom.left) (r : c ⟶ d)
      (O : RefinementFiniteLevelOrigin C.l E n hn X.obj.left),
      (theta c d r).app O =
        refinementComparisonIsomorphism D.k C.l (sfPackageCoefficientIsUnit D C) E n hn f.hom.left
          r O) ∧
    (∀ c : Compactification f.hom.left, theta c c (𝟙 c) = Iso.refl _) ∧
    (∀ (c d e : Compactification f.hom.left) (r : c ⟶ d) (s : d ⟶ e),
      theta c e (r ≫ s) = theta c d r ≪≫ theta d e s) ∧
    ∃ comparison : ∀ c d : Compactification f.hom.left,
      compactificationOriginCandidate C.l E n hn c ≅
        compactificationOriginCandidate C.l E n hn d,
      (∀ (c d e : Compactification f.hom.left) (r : e ⟶ c) (s : e ⟶ d),
        comparison c d = (theta e c r).symm ≪≫ theta e d s) ∧
      (∀ c d e : Compactification f.hom.left,
        comparison c d ≪≫ comparison d e = comparison c e) := by
  sorry

/-- The finite, completed, rational, and common-stage compositors satisfy unit and
associativity equations. Localization and inclusion send the actual components to
the same components in their prescribed object models. Integral reduction to the
finite origin maps is stated separately in sfPackageCompactifiedTowerNormalizedReduction;
enlarged field presentations are stated in sfPackageCompactifiedTowerFieldPassage.
Source: blueprint prop-functor-package, clauses (2)--(3)
(blueprint: lem-sf-package-compactified-tower-comparisons).

Proof: finite composition and its units and associativity are thm-sf-comp-composition,
with its inverse direction. For integral inputs use lem-sf-cbc-compact-support-composition-limit
and lem-pur-completed-coefficient-pushforward-comparison to identify each completed
word with its entire strict tower. The coefficient hypotheses follow from
lem-weil-l-adic-extension-integers-dvr and lem-weil-pbc-standard-quotients-perfect;
finite-type schemes are Noetherian by lem-weil-pbc-finite-type-over-noetherian.
Apply lem-cbc-strict-tower-proper-open-calculus first to a refinement square and then
to compatible compactification towers from lem-cbc-compactifiable-compatible-tower.
Pasting gives independence, units and associativity before evaluation. Apply the
exact total limit from lem-weil-pbc-ringed-strict-tower-homotopy-limit and use
lem-fix-compactification-completed-realization for the same word realization at each
vertex: middle inverse pairs cancel. The
normalizations in lem-fix-operation-reduction identify every reduction with its
finite map. Finally prop-weil-pbc-rational-transport and prop-weil-pbc-descent-functors
carry these equalities to the lattice and common-stage presentations. For descent
use StageSystem.Morphism.functor and descNatTrans with their common-stage formulas;
they preserve these equations and include identity field extensions. -/
theorem sfPackageCompactifiedTowerStageCoherence :
    @SfPackageCompactSupportCoherence.{u, u + 2, u + 2} D
      (sixFunctorFiniteCategory D C E n hn)
      (fun X ↦ inferInstanceAs (Category.{u + 2} (sixFunctorFiniteCategory D C E n hn X)))
      S.finite ∧
    SfPackageCompactSupportCoherence S.higher.integral ∧
    SfPackageCompactSupportCoherence S.higher.rational ∧
    SfPackageCompactSupportCoherence S.closure.commonStage ∧
    SfPackageSupportCoefficientLaws S.higher.integral S.higher.rational
      (fun X ↦ sfRationalConstructibleLocalization C.l E X.obj.left) ∧
    (∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
      SfPackageCompactSupportCoherence (S.closure.coefficientStages E₀).integral ∧
      SfPackageCompactSupportCoherence (S.closure.coefficientStages E₀).rational ∧
      SfPackageSupportCoefficientLaws (S.closure.coefficientStages E₀).integral
        (S.closure.coefficientStages E₀).rational
        (fun X ↦ sfRationalConstructibleLocalization C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left) ∧
      SfPackageSupportCoefficientLaws (S.closure.coefficientStages E₀).rational
        S.closure.commonStage
        (fun X ↦ GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀)) := by
  sorry

/-- The canonical inclusion of an enlarged field presentation, followed by the
actual common-stage operation. The stage-system transIso identifies the enlarged
presentation with the original one, including identity extensions.
Source: blueprint prop-functor-package, common-stage coefficient passage
(blueprint: lem-sf-package-compactified-tower-comparisons). -/
def sfPackageCommonStageSupportTransport
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    {E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E₀ ≤ L)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left E₀) :=
  ((S.closure.commonStageComparison L).supportAdjunction f c).left.app
      (((GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar X.obj.left
        ).T h).obj K) ≪≫
    (S.closure.commonStage.support f c).mapIso
      (((GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar X.obj.left
        ).transIso h).app K)

/-- The same transport for a two-letter field support word. Its two factors are
exactly the inclusion of the outer operation and the inner support transport.
Source: blueprint prop-functor-package, field composition passage
(blueprint: lem-sf-package-compactified-tower-comparisons). -/
def sfPackageCommonStageCompositeTransport
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    {E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E₀ ≤ L)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left E₀) :=
  ((S.closure.commonStageComparison L).supportAdjunction g cg).left.app
      (((S.closure.coefficientStages L).rational.support f cf).obj
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar X.obj.left
          ).T h).obj K)) ≪≫
    (S.closure.commonStage.support g cg).mapIso
      (sfPackageCommonStageSupportTransport D C E n hn S f cf h K)

/-- Direct-image version of the same canonical common-stage transport, retaining
its right-adjoint operation comparison and the stage-system presentation isomorphism.
Source: blueprint prop-functor-package, field proper coincidence passage
(blueprint: lem-sf-package-compactified-tower-comparisons). -/
def sfPackageCommonStageDirectTransport
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    {E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E₀ ≤ L)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left E₀) :=
  ((S.closure.commonStageComparison L).directAdjunction f).right.app
      (((GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar X.obj.left
        ).T h).obj K) ≪≫
    (S.closure.commonStage.direct f).mapIso
      (((GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar X.obj.left
        ).transIso h).app K)

/-- In every enlarged field presentation the actual refinement, compositor and
proper-identity components represent the same common-stage maps. The three transports
above use the actual inclusion and transIso, not coefficientTransition's law fields.
Source: blueprint prop-functor-package, coefficient passage in clauses (2)--(3)
(blueprint: lem-sf-package-compactified-tower-comparisons).

Proof: first localize the normalized integral refinement and composition equations;
on a pure tensor the map is the original component tensored with one. The common
stage inclusion sends it to that same representative. On any enlarged field stage,
apply this model formula at that stage and use the canonical transIso identifying
its inclusion with the original presentation. Naturality moves transIso past the
common-stage comparison, respectively past each of the two support factors in a
composition. The middle transports cancel. For proper identity use the ordinary
right-adjoint comparison for the target transport and the same identity-open unit.
The unitor of the stage system gives exactly the same equations when h is reflexive. -/
theorem sfPackageCompactifiedTowerFieldPassage :
    (∀ (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
      (f : X ⟶ Y) (c d : Compactification f.hom.left)
      (E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E₀ ≤ L)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left E₀),
      (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) L).map
          (((S.closure.coefficientStages L).rational.comparison f c d).hom.app
            (((GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar X.obj.left
              ).T h).obj K)) ≫
        (sfPackageCommonStageSupportTransport D C E n hn S f d h K).hom =
      (sfPackageCommonStageSupportTransport D C E n hn S f c h K).hom ≫
        (S.closure.commonStage.comparison f c d).hom.app
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj K)) ∧
    (∀ (X Y Z : SixFunctorSpace D)
      [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom] [IsSeparated Z.obj.hom]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
      (cfg : Compactification (f ≫ g).hom.left)
      (E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E₀ ≤ L)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left E₀),
      (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := Z.obj.left) L).map
          (((S.closure.coefficientStages L).rational.composition f g cf cg cfg).hom.app
            (((GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar X.obj.left
              ).T h).obj K)) ≫
        (sfPackageCommonStageCompositeTransport D C E n hn S f g cf cg h K).hom =
      (sfPackageCommonStageSupportTransport D C E n hn S (f ≫ g) cfg h K).hom ≫
        (S.closure.commonStage.composition f g cf cg cfg).hom.app
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj K)) ∧
    (∀ (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
      (f : X ⟶ Y) [IsProper f.hom.left]
      (E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E₀ ≤ L)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left E₀),
      (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) L).map
          (((S.closure.coefficientStages L).rational.properIdentity f).hom.app
            (((GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar X.obj.left
              ).T h).obj K)) ≫
        (sfPackageCommonStageDirectTransport D C E n hn S f h K).hom =
      (sfPackageCommonStageSupportTransport D C E n hn S f (.ofIsProper f.hom.left) h K
        ).hom ≫ (S.closure.commonStage.properIdentity f).hom.app
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj K)) := by
  sorry

/-- Integral direct image and compact support reduce by their actual projection counits.
There is no finite-Tor hypothesis on K, and no common Tor interval is imposed.
Source: blueprint prop-functor-package, the two integral reduction formulas
(blueprint: lem-sf-package-compactified-tower-comparisons).

Proof: lem-sf-integral-direct-image-constructible gives the first canonical comparison.
For the second use lem-fix-operation-reduction and the normalized completed proper/open
realization of def-weil-integral-rational-qbar-compact-support. Their finite adjunction
units identify the ordered proper projection/open tensor map with the adjunct of the
chosen Roos projection. lem-sf-integral-compact-support-constructible gives membership
of the limit in the integral constructible category. The transition equation follows
from the quotient cocycle before applying the tensor adjunction. -/
theorem sfPackageCompactifiedTowerIntegralReduction
    (X Y : Scheme.{u}) [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (K : sfIntegralConstructibleCategory C.l E X)
    [HasProduct (sfDirectImageTerm C.l E f K.obj)]
    [HasProduct (sfCompactSupportTerm C.l E c K.obj)]
    (L : SfIntegralDirectImage C.l E f K.obj)
    (M : DerivedCategory (scalarReductionSource C.l E Y))
    (p : M ⟶ ∏ᶜ (sfCompactSupportTerm C.l E c K.obj))
    (δ : (∏ᶜ (sfCompactSupportTerm C.l E c K.obj)) ⟶ M⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle (sfCompactSupportTransition C.l E c K.obj) M p δ) :
    (∀ m : ℕ, IsIso (sfDirectImageReductionComparison C.l E f L m)) ∧
    (∀ m : ℕ, IsIso (coefIntegralCompactSupportComparison C.l E c K.obj M p m)) ∧
    sfIntegralConstructible C.l E Y L.obj ∧ sfIntegralConstructible C.l E Y M ∧
    (∀ m : ℕ,
      coefIntegralCompactSupportComparison C.l E c K.obj M p (m + 1) ≫
          coefCompactSupportFiniteTransition C.l E c K.obj m =
        sfCompactSupportReductionTransition C.l E Y M m ≫
          (sfCompactSupportFiniteRestriction C.l E Y m).mapDerivedCategory.map
            (coefIntegralCompactSupportComparison C.l E c K.obj M p m)) := by
  sorry

/-- The two coefficient maps for A_n to A_m are invertible on bounded constructible
finite-Tor inputs. The ordinary map is the actual fixed-scalar counit mate in the
canonical inverse realization; the support map is the actual intrinsic scalar mate.
Source: blueprint prop-functor-package, finite quotient comparison sentence
(blueprint: lem-sf-package-compactified-tower-comparisons).

Proof: realize the bounded constructible input at its retained etale origin using
lem-weil-pbc-finite-ring-constructible-derived-origin. Tor amplitude agrees by
lem-sf-comparison-tor-amplitude. The quotient A_m is finite over A_n, generated by 1,
so lem-coef-finite-direct-image applies to the counit-defined ordinary map.
lem-fix-compact-support-coefficient-change applies to the same input and its universal
tensor presentations. The canonical scalar equivalences preserve these mates.
The argument includes m=n and requires no flatness of the quotient. -/
theorem sfPackageCompactifiedTowerFiniteReduction
    (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left]
    [QuasiCompact f.hom.left] (c : Compactification f.hom.left)
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (hK : finiteTorConstructible C.l E n hn X.obj.left K.obj) :
    IsIso (finiteCoefficientChangeDirectImageMap
      (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
        (S := Padic.coefficientExtensionIdeal C.l E n)
        (T := Padic.coefficientExtensionIdeal C.l E m) (Ideal.pow_le_pow_right hmn)))
      f.hom.left ((sixFunctorFiniteRealization D C E n hn X).inverse.obj K.obj)) ∧
    IsIso (finiteLevelCompactSupportReductionComparison C.l E m n hm hmn c K.obj) := by
  sorry

/-- The actual counit reconstructs every coherent normalized tower, without finiteness
assumptions. A common finite constructible cohomological interval gives integral membership.
Source: blueprint prop-functor-package, normalized tower reconstruction sentence
(blueprint: lem-sf-package-compactified-tower-comparisons).

Proof: lem-coef-normalized-dvr-effectivity identifies the scalar adjunct of each Roos
projection with the finite reduction. It proves invertibility and the quotient cocycle,
and identifies the canonical augmentation with the completion unit. If the finite terms
are constructible in one interval [a,b], transport constructibility and support along
these same counit isomorphisms. Completeness and that one common interval are precisely
def-weil-derived-complete-integral-detailed. No boundedness is used for effectivity itself. -/
theorem sfPackageCompactifiedTowerEffectivity
    (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (T : NormalizedDVRTower C.l E Y D C.different)
    (M : completedIntegralDerivedCategory C.l E Y D C.different)
    [HasProduct (fun m : ℕ ↦
      (normalizedDVRTowerEvaluation C.l E Y D C.different m).obj T.tower)]
    (p : M ⟶ ∏ᶜ fun m : ℕ ↦
      (normalizedDVRTowerEvaluation C.l E Y D C.different m).obj T.tower)
    (δ : (∏ᶜ fun m : ℕ ↦
      (normalizedDVRTowerEvaluation C.l E Y D C.different m).obj T.tower) ⟶ M⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle
      (fun m : ℕ ↦ (normalizedDVRTowerTransition C.l E Y D C.different m.le_succ).app
        T.tower) M p δ) :
    (∀ m : ℕ, IsIso (normalizedDVRCounitComparison C.l E Y D C.different T M p m)) ∧
    (∀ (r m : ℕ) (h : m ≤ r),
      normalizedDVRCounitComparison C.l E Y D C.different T M p r ≫ T.tau h =
        normalizedDVRReductionTransition C.l E Y D C.different h M ≫
          (normalizedDVRRes C.l E Y h).map
            (normalizedDVRCounitComparison C.l E Y D C.different T M p m)) ∧
    IsDerivedComplete C.l E Y D C.different M ∧
    ((∃ a b : ℤ, a ≤ b ∧ ∀ m : ℕ,
      intrinsicFiniteTorsionConstructible C.l E (m + 1)
        (Nat.succ_le_succ (Nat.zero_le m)) Y (T.M m) ∧
      proEtaleCohomologicalSupport (T.M m) ⊆ Set.Icc a b) →
        sfIntegralConstructible C.l E Y M) := by
  sorry

/-- The finite identity-open isomorphism, restricted to completed coefficients.
Source: blueprint prop-functor-package, proper strict quotient towers
(blueprint: lem-sf-package-compactified-tower-comparisons). -/
def sfPackageProperLevelComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (K : DerivedCategory (scalarReductionSource C.l E X)) (m : ℕ) :
    sfCompactSupportTerm C.l E (.ofIsProper f) K m ≅ sfDirectImageTerm C.l E f K m :=
  (scalarReductionDerivedRestriction C.l E Y m).mapIso
    ((@sixFunctorProperCandidateIso (Padic.coefficientExtensionRing C.l E (m + 1)) _
      (Padic.finite_coefficientExtensionRing C.l E (m + 1)
        (Nat.succ_le_succ (Nat.zero_le m))) X Y f _).app
      ((scalarReductionDerivedExtension C.l E X m).obj K))

/-- The chosen support projection transported along the datum's retained value
identification. This is exactly the projection whose tensor adjunct is the chosen
support reduction. Source: blueprint prop-functor-package, proper-coincidence paragraph
(blueprint: lem-sf-package-compactified-tower-comparisons). -/
def sfPackageIntegralSupportProjection
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    ((S.higher.integral.support f c).obj K).obj ⟶
      ∏ᶜ (sfCompactSupportTerm C.l E c K.obj) := by
  letI : HasCountableProducts
      (DerivedCategory (scalarReductionSource C.l E Y.obj.left)) :=
    integralOperationsDerivedCountableProducts C.l E Y.obj.left
  exact (sfIntegralConstructible C.l E Y.obj.left).ι.map
      (eqToHom ((S.higher.supportConstruction f (sfPackageCoefficientIsUnit D C) c
        ).choose_spec.2.2.1 K)) ≫
    Classical.choose (Classical.choose_spec (exists_isDerivedLimit_and_iso
      (sfCompactSupportTerm C.l E c K.obj)
      (sfCompactSupportTransition C.l E c K.obj)).1)

/-- The actual datum proper identification, in its retained ordinary limit coordinates.
This is constructed from integral.properIdentity itself, with no existential choice
of a morphism of triangles. Source: blueprint prop-functor-package, proper coincidence
(blueprint: lem-sf-package-compactified-tower-comparisons). -/
def sfPackageIntegralProperLimitIso
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    [HasProduct (sfDirectImageTerm C.l E f.hom.left K.obj)] :=
  (sfIntegralConstructible C.l E Y.obj.left).ι.mapIso
      ((S.higher.integral.properIdentity f).app K) ≪≫
    eqToIso (S.higher.integralDirectLimitObject f K).symm

/-- Proper coincidence identifies the strict quotient-transition towers and their
specified derived limits by the actual integral proper identity of the datum.
Source: blueprint prop-functor-package, final proper-coincidence paragraph
(blueprint: lem-sf-package-compactified-tower-comparisons).

Proof: on each finite quotient the canonical identity-open unit gives precisely
sfPackageProperLevelComparison. Naturality of that unit in coefficient restriction
identifies the two actual quotient transitions. This is an equality of strict tower
maps before evaluation, by lem-cbc-strict-tower-proper-open-calculus. Apply total
inverse limit, using lem-fix-compactification-completed-realization to retain the
support projection and lem-pur-completed-coefficient-pushforward-comparison to retain
the ordinary projection. The normalization supportProjection/directProjection and
finiteProperNormalization of the operation datum identify this limit map with its
integral.properIdentity. Thus the displayed isomorphism is that very proper identity,
not an unrelated isomorphism obtained by completing a square of triangles. Its
projection equations identify it with the limit of the strict identity-open map. -/
theorem sfPackageCompactifiedTowerProperTransitions
    (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsProper f.hom.left]
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    (∀ m : ℕ,
      sfCompactSupportTransition C.l E (.ofIsProper f.hom.left) K.obj m ≫
          (sfPackageProperLevelComparison D C E f.hom.left K.obj m).hom =
        (sfPackageProperLevelComparison D C E f.hom.left K.obj (m + 1)).hom ≫
          sfDirectImageTransition C.l E f.hom.left K.obj m) ∧
    (∀ [HasProduct (sfDirectImageTerm C.l E f.hom.left K.obj)] (m : ℕ),
      (sfPackageIntegralProperLimitIso D C E n hn S f K).hom ≫
          (S.higher.integralDirectLimit f K).projection ≫ Pi.π _ m =
        sfPackageIntegralSupportProjection D C E n hn S f (.ofIsProper f.hom.left) K ≫
          Pi.π _ m ≫ (sfPackageProperLevelComparison D C E f.hom.left K.obj m).hom) := by
  sorry

/-- The identity-open comparison in the fixed-scalar unbounded derived presentation.
It is formed from the specified open adjunction and its ordinary unit.
Source: blueprint prop-functor-package, proper identity compactification
(blueprint: lem-sf-package-compactified-tower-comparisons). -/
def sfPackageFixedProperIdentity (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (.ofIsProper f) ≅ (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor :=
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryNatIso
      (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
        (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
      Functor.mapDerivedCategoryIdIso _) _ ≪≫ Functor.leftUnitor _

/-- Proper identification of a candidate on its retained fixed-scalar origin witness.
Both transports use that same witness; the middle comparison is the recorded etale
compactification comparison. This defines a map, without choosing from Nonempty.
Source: blueprint prop-functor-package, proper comparison on the witnessed domain
(blueprint: lem-sf-package-compactified-tower-comparisons). -/
def sfPackageFixedProperIdentification (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (c : Compactification f)
    (K : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)))
    (O : FixedEtaleOriginWitness X A K) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K.obj ≅
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj K.obj :=
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).mapIso O.iso.symm ≪≫
    (rightDerivedLowerShriekOfCompactificationOriginIso A c (.ofIsProper f)).app O.complex ≪≫
    (sfPackageFixedProperIdentity A f).app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj O.complex.obj) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.mapIso O.iso

/-- The proper comparison on a base-changed candidate; properness of f' is obtained
from the given Cartesian square, rather than imposed as an extra hypothesis.
Source: blueprint prop-functor-package, proper base change
(blueprint: lem-sf-package-compactified-tower-comparisons). -/
def sfPackageFixedBaseChangedProperIdentification
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [IsProper f]
    (sq : IsPullback g' f' f g)
    (N : DerivedCategory.Plus (Sheaf (ProEt.topology X') (ModuleCat.{u + 1} A)))
    (O : FixedEtaleOriginWitness X' A N) :=
  letI : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance
  sfPackageFixedProperIdentification A f'
    ((Compactification.ofIsProper f).ofIsPullback sq) N O

/-- The fixed-scalar proper-exchange equation, including every presentation of the
pulled-back input. This only packages the equation; no origin or comparison is chosen.
Source: blueprint prop-functor-package, proper-exchange sentence
(blueprint: lem-sf-package-compactified-tower-comparisons). -/
def SfPackageFixedProperExchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [IsProper f]
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) : Prop :=
    (∃ N : DerivedCategory.Plus (Sheaf (ProEt.topology X') (ModuleCat.{u + 1} A)),
      Nonempty (N.obj ≅ ((upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor).obj K.obj) ∧
      Nonempty (FixedEtaleOriginWitness X' A N)) ∧
    (∀ (N : DerivedCategory.Plus (Sheaf (ProEt.topology X') (ModuleCat.{u + 1} A)))
      (e : N.obj ≅ ((upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor).obj K.obj)
      (O' : FixedEtaleOriginWitness X' A N),
      (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.map
          ((sfPackageFixedProperIdentity A f).hom.app K.obj) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app K.obj =
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} A) sq
            (.ofIsProper f)).app K.obj ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          ((Compactification.ofIsProper f).ofIsPullback sq)).map e.inv ≫
        (sfPackageFixedBaseChangedProperIdentification A sq N O').hom ≫
        (lowerStar (ModuleCat.{u + 1} A) f').rightDerivedFunctor.map e.hom)

/-- On the witnessed pro-etale domain, proper coincidence identifies the actual Ex_!
with the actual proper-base-change mate Ex_*. Pullback retains an origin witness;
the equation is required for every presentation of this pullback, not a chosen lift.
Source: blueprint prop-functor-package, proper-exchange sentence
(blueprint: lem-sf-package-compactified-tower-comparisons).

Proof: pull back the retained etale antecedent and use the canonical comparison
pullback isomorphism, giving the displayed witness. In the identity-open model the
beta factor in def-exchange-projection is the identity-open unit comparison. Cancel
its unit with the two proper identifications. The remaining map is exactly the
unit--square--counit mate Ex_*. cor-cbc-proper-coincidence proves this on etale
antecedents; canonical site comparison gives the displayed pro-etale equation.
Naturality gives independence of the retained presentation and its endpoint iso. -/
theorem sfPackageCompactifiedTowerFiniteProperExchange
    (m : ℕ)
    {X X' Y Y' : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [X'.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] [Y'.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (X' ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [IsSeparated (Y' ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of D.k))] [QuasiCompact (X' ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of D.k))] [QuasiCompact (Y' ↘ Spec (.of D.k))]
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [IsProper f]
    [f.IsOver (Spec (.of D.k))] [f'.IsOver (Spec (.of D.k))]
    [g.IsOver (Spec (.of D.k))] [g'.IsOver (Spec (.of D.k))]
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing C.l E (m + 1))))))
    (O : FixedEtaleOriginWitness X (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1)))
      K) :
    SfPackageFixedProperExchange
      (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1))) sq K := by
  sorry

/-- The prescribed supplied-stage proper identification on the base-changed map.
The Cartesian square proves properness. Source: blueprint prop-functor-package,
proper exchange (blueprint: lem-sf-package-compactified-tower-comparisons). -/
def sfPackageStageBaseChangedProperIdentification
    {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type v}
    [∀ X, Category.{w} (B X)] (P : SixFunctorPushStage D B)
    (Q : SixFunctorCompactifiedSquare D) [IsProper Q.f.hom.left] :=
  letI : IsProper Q.f'.hom.left :=
    MorphismProperty.of_isPullback (P := @IsProper) Q.square inferInstance
  P.properIdentification Q.f' Q.compactification'

/-- The supplied proper-exchange equation, using the prescribed proper comparisons
of the same operation stage. Endpoint transports only use the recorded stage equalities.
Source: blueprint prop-functor-package, proper coincidence under coefficient passage
(blueprint: lem-sf-package-compactified-tower-comparisons). -/
def SfPackageProperExchangeLaws
    {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type v}
    [∀ X, Category.{w} (B X)] (P : SixFunctorPushStage D B)
    (T : ∀ X, B X ⥤ B X ⥤ B X)
    (ex : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData P T Q) : Prop :=
  ∀ (Q : SixFunctorCompactifiedSquare D)
    [IsSeparated Q.X.obj.hom] [IsSeparated Q.Y.obj.hom]
    [IsSeparated Q.X'.obj.hom] [IsSeparated Q.Y'.obj.hom]
    [IsProper Q.f.hom.left],
    ∃ (e : (ex Q).stage.compactSupport ≅ (ex Q).stage.push)
      (e' : (ex Q).stage.compactSupport' ≅ (ex Q).stage.push'),
    e = eqToIso (ex Q).compactSupport ≪≫ P.properIdentification Q.f Q.compactification ≪≫
      eqToIso (ex Q).push.symm ∧
    e' = eqToIso (ex Q).compactSupport' ≪≫
      sfPackageStageBaseChangedProperIdentification P Q ≪≫ eqToIso (ex Q).push'.symm ∧
    Functor.whiskerRight e.hom (ex Q).stage.horizontal ≫ (ex Q).stage.exchange =
      (ex Q).stage.compactExchange ≫ Functor.whiskerLeft (ex Q).stage.horizontal' e'.hom

/-- The completed proper exchange and its lattice and common-stage representatives
are the ordinary exchanges under the same canonical proper identifications.
Source: blueprint prop-functor-package, final two sentences
(blueprint: lem-sf-package-compactified-tower-comparisons).

Proof: expand def-cbc-completed-exchange-map at the identity-open compactification.
The identity-open beta cancels. The two strict quotient-transition towers have the
same terms and maps by sfPackageCompactifiedTowerProperTransitions, and their limit
identification is sfPackageIntegralProperLimitIso. Apply total derived limit to this
identity, retaining the fixed projections and normalization of ordinary pushforward
from lem-pur-completed-coefficient-pushforward-comparison. Thus the completed exchange
is the ordinary completed mate. The normalized realization of the operation datum
identifies it with the supplied exchange formula. Rational transport tensors each
component with 1 and common-stage descent takes its finite-field representative,
so both field equations follow with no additional Tor bound. -/
theorem sfPackageCompactifiedTowerHigherProperExchange :
    SfPackageProperExchangeLaws S.higher.integral S.higher.integralTensor
      S.higher.integralExchange ∧
    SfPackageProperExchangeLaws S.higher.rational S.higher.rationalTensor
      S.higher.rationalExchange ∧
    SfPackageProperExchangeLaws S.closure.commonStage S.closure.commonStageTensor
      S.closure.commonStageExchange ∧
    (∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
      SfPackageProperExchangeLaws (S.closure.coefficientStages E₀).integral
        (S.closure.coefficientStages E₀).integralTensor
        (S.closure.coefficientStages E₀).integralExchange ∧
      SfPackageProperExchangeLaws (S.closure.coefficientStages E₀).rational
        (S.closure.coefficientStages E₀).rationalTensor
        (S.closure.coefficientStages E₀).rationalExchange) := by
  sorry

end WeilConjectures
