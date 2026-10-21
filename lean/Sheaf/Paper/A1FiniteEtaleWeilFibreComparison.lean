/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.Paper.SfCommonStageDirectImage
public import Sheaf.Paper.ConstantExtensionWeilHeartEquivalence
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.GlobalGeometricFrobenius
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.AlgebraicGeometry.FiniteMorphismsConstructible
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.NormalizedDVRTower
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.SixFunctors.OpenFactorCoherence
import Sheaf.Paper.ZlFiniteAdicDirectImage
import Sheaf.Paper.ConstructibleTruncations
import Sheaf.Paper.DlConstructibleFibresExact
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.ConstructiblePullbackTExact
import Sheaf.Paper.IntegralPullbackComposition
import Sheaf.Paper.ProperCoincidenceFrobenius
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
import Sheaf.SixFunctors.FrobeniusCohomologyTransportIso
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients

/-! # Finite etale Weil fibre comparison

Source: Stacks 03QP(1)--(2); Deligne, Weil II (1.1.3), (1.1.7)--(1.1.10);
main-20261015, lem-a1-finite-map-purity.proof.md, first paragraph
(blueprint: lem-a1-finite-etale-weil-fibre-comparison).

The comparison is the counit mate on the actual common-stage categories. Its target
is represented by the proper direct image to Spec(kappa(y)). The point-fibre convention
identifies this degree-zero object with compact cohomology, including its Weil action.
In particular no arbitrary stalk isomorphism is supplied as a hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u})
  (Y₀ : Over (Spec (.of D.k₀))) [hYft : LocallyOfFiniteType Y₀.hom] [hYqc : QuasiCompact Y₀.hom]
  (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
  (ι : Y₀.left.residueField y.val →+* D.k)
  (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)

include hι hYft hYqc in
/-- The actual residue field is finite of degree d_y and has the chosen closure via ι.
Source: Stacks 03QP fibre; lem-kun-closed-point-field; Weil II (1.1.7)
(blueprint: lem-a1-finite-etale-weil-fibre-comparison).
Proof: Zariski's lemma makes kappa(y) finite over k_0. Its cardinality is q^d_y.
The compatible embedding makes k an algebraic extension of kappa(y), and k is already
algebraically closed. Thus it is the specified algebraic closure of that residue field. -/
theorem a1ResidueField_properties :
    Finite (Y₀.left.residueField y.val) ∧
      Nat.card (Y₀.left.residueField y.val) = D.q ^ localClosedPointDegree D Y₀ y ∧
      @IsAlgClosure (Y₀.left.residueField y.val) D.k _ _ ι.toAlgebra _ := by
  sorry

/-- The finite-field datum for L=kappa(y), retaining the chosen embedding into k.
Source: Weil II (1.1.7)--(1.1.10), change of finite base field
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1ResidueDatum : FiniteFieldDatum.{u} where
  p := D.p
  a := D.a * localClosedPointDegree D Y₀ y
  q := D.q ^ localClosedPointDegree D Y₀ y
  prime := D.prime
  exponent_pos := le_trans (localClosedPointDegree_pos D Y₀ y)
    (Nat.le_mul_of_pos_left _ D.exponent_pos)
  cardinality_eq := D.cardinality_eq ▸ (pow_mul D.p D.a _).symm
  k₀ := Y₀.left.residueField y.val
  finite_base := (a1ResidueField_properties D Y₀ y ι hι).1
  card_base := (a1ResidueField_properties D Y₀ y ι hι).2.1
  k := D.k
  algebra_closure := ι.toAlgebra
  isAlgClosure := (a1ResidueField_properties D Y₀ y ι hι).2.2

/-- The residue-point morphism has the structural field map stated in the node.
Source: scheme residue-field convention and Stacks 03QP
(blueprint: lem-a1-finite-etale-weil-fibre-comparison).
Proof: the composite from Spec(kappa(y)) to Spec(k_0) is Spec of the map on residue
fields. This is the functorial defining property of fromSpecResidueField. -/
theorem a1ResiduePoint_over :
    Y₀.left.fromSpecResidueField y.val ≫ Y₀.hom =
      Spec.map (CommRingCat.ofHom (Y₀.hom.residueFieldAlgebraMap y.val)) := by
  sorry

variable (T₀ : Over (Spec (.of (Y₀.left.residueField y.val))))
  [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  (j₀ : T₀.left ⟶ X₀.left)
  (hj : j₀ ≫ X₀.hom = T₀.hom ≫
    Spec.map (CommRingCat.ofHom (Y₀.hom.residueFieldAlgebraMap y.val)))

include hι hj in
/-- Compatibility of the two projections defining geometric restriction to the fibre.
Source: Stacks 03QP and the chosen residue embedding
(blueprint: lem-a1-finite-etale-weil-fibre-comparison).
Proof: substitute hj, use the pullback projection equation, and apply Spec to hι. -/
theorem a1ResidueInclusion_compatible :
    (pullback.fst T₀.hom (Spec.map (CommRingCat.ofHom ι)) ≫ j₀) ≫ X₀.hom =
      pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom ι)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  sorry

/-- The canonical geometric restriction map, defined by its two pullback projections.
Source: Stacks 03QP fibre and Weil II (1.1.7)
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1ResidueInclusion :
    ((a1ResidueDatum D Y₀ y ι hι).geometricFiber T₀).left ⟶
      (D.geometricFiber X₀).left :=
  pullback.lift
    (pullback.fst T₀.hom (Spec.map (CommRingCat.ofHom ι)) ≫ j₀)
    (pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom ι)))
    (a1ResidueInclusion_compatible D Y₀ y ι hι T₀ X₀ j₀ hj)

/-- The residue-field Frobenius is the d_y-fold original Frobenius after restriction.
Source: Weil II (1.1.7)--(1.1.10)
(blueprint: lem-a1-finite-etale-weil-fibre-comparison).
Proof: the residue field has q^d_y elements. Its geometric Frobenius on k is gamma^d_y.
Both sides have the same projection to T_0 and the same map on k; pullback uniqueness
therefore identifies them. This is a semilinear return, not pointwise fixedness. -/
theorem a1ResidueInclusion_return :
    ((a1ResidueDatum D Y₀ y ι hι).geometricFrobenius T₀).hom ≫
        a1ResidueInclusion D Y₀ y ι hι T₀ X₀ j₀ hj =
      a1ResidueInclusion D Y₀ y ι hι T₀ X₀ j₀ hj ≫
        localPositivePower (D.geometricFrobenius X₀).hom
          (localClosedPointDegree D Y₀ y - 1) := by
  sorry

variable (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Pullback along the canonical geometric restriction, on the existing pair categories.
Source: Stacks 03QP fibre restriction
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1ResiduePull :=
  @commonStageDerivedPullback l _ Ω _ _ _ _ _
    (a1ResidueInclusion D Y₀ y ι hι T₀ X₀ j₀ hj)
    (sfWeilPrimeInvertible (a1ResidueDatum D Y₀ y ι hι) l hl T₀)
    (sfWeilPrimeInvertible D l hl X₀)

/-- The normalized comparison from residue Frobenius to the original d_y-th pullback.
Source: Weil II (1.1.7)--(1.1.10); prescribed integral pullback composition
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1ResidueReturnComparison
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left) :=
  letI := sfWeilPrimeInvertible (a1ResidueDatum D Y₀ y ι hι) l hl T₀
  letI := sfWeilPrimeInvertible D l hl X₀
  ((zlPullComp l Ω
    ((a1ResidueDatum D Y₀ y ι hι).geometricFrobenius T₀).hom
    (a1ResidueInclusion D Y₀ y ι hι T₀ X₀ j₀ hj)).app M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (commonStageDerivedPullback l Ω f).obj M)
      (a1ResidueInclusion_return D Y₀ y ι hι T₀ X₀ j₀ hj)) ≪≫
    (zlPullComp l Ω (a1ResidueInclusion D Y₀ y ι hι T₀ X₀ j₀ hj)
      (localPositivePower (D.geometricFrobenius X₀).hom
        (localClosedPointDegree D Y₀ y - 1))).app M

/-- Restriction with the degree-d_y iterated Weil structure and canonical return comparison.
Source: Weil II (1.1.7)--(1.1.10)
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1ResidueWeilComplex (F : sfCommonStageWeilComplex D l hl X₀ Ω) :
    sfCommonStageWeilComplex (a1ResidueDatum D Y₀ y ι hι) l hl T₀ Ω :=
  IsoAlgebra.mk ((a1ResiduePull D Y₀ y ι hι T₀ X₀ j₀ hj l hl Ω).obj F.carrier)
    (a1ResidueReturnComparison D Y₀ y ι hι T₀ X₀ j₀ hj l hl Ω F.carrier ≪≫
      (a1ResiduePull D Y₀ y ι hι T₀ X₀ j₀ hj l hl Ω).mapIso
        (constantExtensionWeilIterate D l hl Ω X₀ F (localClosedPointDegree D Y₀ y - 1)))


variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Finite-stage restriction uses the same geometric map and the recorded rational pullback.
Source: Weil II (1.1.3), (1.1.7)--(1.1.10)
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1ResidueRationalPull :=
  @rationalDerivedPullback l _ E _ _ _ _ _
    (a1ResidueInclusion D Y₀ y ι hι T₀ X₀ j₀ hj)
    (sfWeilPrimeInvertible (a1ResidueDatum D Y₀ y ι hι) l hl T₀)
    (sfWeilPrimeInvertible D l hl X₀)

/-- The rational return comparison is the localization of the integral compositor.
Source: Weil II (1.1.3), (1.1.7)--(1.1.10)
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1ResidueRationalReturnComparison
    (M : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :=
  letI := sfWeilPrimeInvertible (a1ResidueDatum D Y₀ y ι hι) l hl T₀
  letI := sfWeilPrimeInvertible D l hl X₀
  (localPullbackComposition l E
    ((a1ResidueDatum D Y₀ y ι hι).geometricFrobenius T₀).hom
    (a1ResidueInclusion D Y₀ y ι hι T₀ X₀ j₀ hj) M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (rationalDerivedPullback l E f).obj M)
      (a1ResidueInclusion_return D Y₀ y ι hι T₀ X₀ j₀ hj)) ≪≫
    localPullbackComposition l E (a1ResidueInclusion D Y₀ y ι hι T₀ X₀ j₀ hj)
      (localPositivePower (D.geometricFrobenius X₀).hom
        (localClosedPointDegree D Y₀ y - 1)) M

/-- The rational finite-stage version of the actual relative-L Weil restriction.
Source: Weil II (1.1.3), (1.1.7)--(1.1.10)
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1ResidueRationalWeilComplex (F : sfWeilComplex D l hl X₀ E) :
    sfWeilComplex (a1ResidueDatum D Y₀ y ι hι) l hl T₀ E :=
  IsoAlgebra.mk ((a1ResidueRationalPull D Y₀ y ι hι T₀ X₀ j₀ hj l hl E).obj F.carrier)
    (a1ResidueRationalReturnComparison D Y₀ y ι hι T₀ X₀ j₀ hj l hl E F.carrier ≪≫
      (a1ResidueRationalPull D Y₀ y ι hι T₀ X₀ j₀ hj l hl E).mapIso
        (localWeilIterate l E D hl X₀ F (localClosedPointDegree D Y₀ y - 1)))

/-- The canonical stalk identification at every geometric lift, before applying H^0.
Source: Stacks 03QP fibre restriction, Weil II (1.1.7)--(1.1.10)
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1ResidueRationalStalkComparison (F : sfWeilComplex D l hl X₀ E)
    (z : Spec (.of D.k) ⟶ ((a1ResidueDatum D Y₀ y ι hι).geometricFiber T₀).left) :
    localPointComplex l E (a1ResidueDatum D Y₀ y ι hι) hl T₀
        (a1ResidueRationalWeilComplex D Y₀ y ι hι T₀ X₀ j₀ hj l hl E F) z ≅
      localPointComplex l E D hl X₀ F
        (z ≫ a1ResidueInclusion D Y₀ y ι hι T₀ X₀ j₀ hj) :=
  letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
    frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible (a1ResidueDatum D Y₀ y ι hι) l hl T₀
  letI := sfWeilPrimeInvertible D l hl X₀
  (pointRationalFibre D l hl E).mapIso
    (@localPullbackComposition l _ E _ _ _ _ _ _ z
      (a1ResidueInclusion D Y₀ y ι hι T₀ X₀ j₀ hj)
      (frobeniusPointPrimeInvertible D l hl)
      (sfWeilPrimeInvertible (a1ResidueDatum D Y₀ y ι hι) l hl T₀)
      (sfWeilPrimeInvertible D l hl X₀) F.carrier).symm

/-- The common-stage restriction of a stage object is literally the stage object of the
finite-stage restriction: both carriers are the specified common-stage pullback object.
Source: Weil II (1.1.3), common-stage convention
(blueprint: lem-a1-finite-etale-weil-fibre-comparison).
Proof: this is the first clause of commonStageDerivedPullback_existsUnique for the
restriction map, evaluated at the stage object of K and read from right to left;
at an object of stage S the specified pullback object is the stage-S rational pullback. -/
theorem a1ResidueStageCarrier_eq (S : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfWeilComplex D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω S)) :
    (GeneralAlgebraicallyClosedCoefficients.inclusion S).obj
      (a1ResidueRationalWeilComplex D Y₀ y ι hι T₀ X₀ j₀ hj l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω S) K).carrier =
      (a1ResidueWeilComplex D Y₀ y ι hι T₀ X₀ j₀ hj l hl Ω
        (sfWeilStageObject D l hl X₀ Ω S K)).carrier := by
  sorry

/-- The common-stage restriction has its actual finite-stage carrier comparison.
Source: Weil II (1.1.3), common-stage convention
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1ResidueStageCarrierIso (S : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfWeilComplex D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω S)) :
    ((GeneralAlgebraicallyClosedCoefficients.inclusion S).obj
      (a1ResidueRationalWeilComplex D Y₀ y ι hι T₀ X₀ j₀ hj l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω S) K).carrier) ≅
      (a1ResidueWeilComplex D Y₀ y ι hι T₀ X₀ j₀ hj l hl Ω
        (sfWeilStageObject D l hl X₀ Ω S K)).carrier :=
  eqToIso (a1ResidueStageCarrier_eq D Y₀ y ι hι T₀ X₀ j₀ hj l hl Ω S K)

/-- The carrier comparison is equivariant for the prescribed iterates, so the local
finite-stage equalities are equalities for G itself, independently of its presentation.
Source: Weil II (1.1.3), (1.1.7)--(1.1.10)
(blueprint: lem-a1-finite-etale-weil-fibre-comparison).
Proof: each pullback comparison at a common stage is the scalar extension of its
integral counterpart. Expand theta^[d_y] and the return comparison; their prescribed
composition and scalar cocycles identify every factor. Thus the carrier comparison
commutes with the Weil structures. Full faithfulness of the fixed-pair forgetful
functor gives uniqueness from the displayed underlying-arrow equality. -/
theorem a1ResidueStageComparison (S : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfWeilComplex D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω S)) :
    ∃! e : sfWeilStageObject (a1ResidueDatum D Y₀ y ι hι) l hl T₀ Ω S
        (a1ResidueRationalWeilComplex D Y₀ y ι hι T₀ X₀ j₀ hj l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω S) K) ≅
      a1ResidueWeilComplex D Y₀ y ι hι T₀ X₀ j₀ hj l hl Ω
        (sfWeilStageObject D l hl X₀ Ω S K),
      e.hom.hom.f = (a1ResidueStageCarrierIso D Y₀ y ι hι T₀ X₀ j₀ hj l hl Ω S K).hom := by
  sorry

end WeilConjectures

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u})
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [hYft : LocallyOfFiniteType Y₀.hom] [hYqc : QuasiCompact Y₀.hom]
  (g₀ : X₀ ⟶ Y₀) [hg : IsFinite g₀.left]
  (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
  (ι : Y₀.left.residueField y.val →+* D.k)
  (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)

/-- Z_0=X_0 times_(Y_0) Spec(kappa(y)), with its second projection to Spec(kappa(y)).
Source: Stacks 03QP fibre (blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1FiniteFibreModel : Over (Spec (.of (Y₀.left.residueField y.val))) :=
  Over.mk (pullback.snd g₀.left (Y₀.left.fromSpecResidueField y.val))

/-- The finite fibre is finite over its actual residue field, also for an empty fibre.
Source: Stacks 03QP fibre and base change of finite morphisms
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
instance a1FiniteFibreModel_finite : IsFinite (a1FiniteFibreModel D g₀ y).hom :=
  inferInstanceAs (IsFinite (pullback.snd g₀.left (Y₀.left.fromSpecResidueField y.val)))

/-- The first projection is over k_0 using the residue-field structure map.
Source: Stacks 03QP fibre (blueprint: lem-a1-finite-etale-weil-fibre-comparison).
Proof: compose the pullback projection equality with Y_0's structure morphism;
use the equality of structural maps for g_0 and a1ResiduePoint_over. -/
theorem a1FiniteFibreProjection_over :
    pullback.fst g₀.left (Y₀.left.fromSpecResidueField y.val) ≫ X₀.hom =
      (a1FiniteFibreModel D g₀ y).hom ≫
        Spec.map (CommRingCat.ofHom (Y₀.hom.residueFieldAlgebraMap y.val)) := by
  sorry

/-- The geometric inclusion Z to X, with both projections fixed by the fibre construction.
Source: Stacks 03QP fibre (blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1FiniteFibreInclusion :=
  a1ResidueInclusion D Y₀ y ι hι (a1FiniteFibreModel D g₀ y) X₀
    (pullback.fst g₀.left (Y₀.left.fromSpecResidueField y.val))
    (a1FiniteFibreProjection_over D g₀ y)

/-- The geometric residue-point lift, in the canonical model over L.
Source: Weil II (1.1.7), chosen geometric-point reparametrization
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1FiniteFibrePointInclusion :=
  a1ResidueInclusion D Y₀ y ι hι (sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι)) Y₀
    (Y₀.left.fromSpecResidueField y.val)
    (by change _ = (𝟙 _) ≫ _;
        rw [Category.id_comp]; exact a1ResiduePoint_over D Y₀ y)

/-- The finite fibre's structure map, bundled as an L-morphism.
Source: Stacks 03QP fibre (blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1FiniteFibreStructure : a1FiniteFibreModel D g₀ y ⟶
    sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι) :=
  Over.homMk (a1FiniteFibreModel D g₀ y).hom

/-- The geometric fibre square commutes with its prescribed point reparametrization.
Source: Stacks 03QP fibre (blueprint: lem-a1-finite-etale-weil-fibre-comparison).
Proof: compare the projections to X_0 and k, using pullback.condition twice.
The residue embedding compatibility is exactly hι. -/
theorem a1FiniteFibreSquare :
    zlFiberMap (a1ResidueDatum D Y₀ y ι hι) (a1FiniteFibreStructure D g₀ y ι hι) ≫
        a1FiniteFibrePointInclusion D y ι hι =
      a1FiniteFibreInclusion D g₀ y ι hι ≫ zlFiberMap D g₀ := by
  sorry

variable (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- G is the actual restriction of F to the fibre with theta^[d_y] and the return map.
Source: Weil II (1.1.7)--(1.1.10), Stacks 03QP fibre
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1FiniteFibreWeilComplex (F : sfCommonStageWeilComplex D l hl X₀ Ω) :=
  a1ResidueWeilComplex D Y₀ y ι hι (a1FiniteFibreModel D g₀ y) X₀
    (pullback.fst g₀.left (Y₀.left.fromSpecResidueField y.val))
    (a1FiniteFibreProjection_over D g₀ y) l hl Ω F

/-- Restriction of the direct-image pair to the residue point with its local return.
Source: Weil II (1.1.7)--(1.1.10), local F_y
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1FiniteFibreStalkPair (F : sfCommonStageWeilComplex D l hl X₀ Ω) :=
  a1ResidueWeilComplex D Y₀ y ι hι (sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι)) Y₀
    (Y₀.left.fromSpecResidueField y.val)
    (by change _ = (𝟙 _) ≫ _;
        rw [Category.id_comp]; exact a1ResiduePoint_over D Y₀ y) l hl Ω
    ((sfModelWeilDerivedPush D l hl Ω g₀).obj F)

/-- The geometric counit of the actual equivariant direct image, using its normalized
forgetful comparison. It contains no freely chosen comparison isomorphism.
Source: Stacks 03QP restriction map; derived-image convention
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1FiniteFibreCounit (F : sfCommonStageWeilComplex D l hl X₀ Ω) :=
  (zlPull D l hl Ω g₀).map ((sfModelWeilDerivedPushForget D l hl Ω g₀).hom.app F) ≫
    (sfModelDerivedAdjunction D l hl Ω g₀).counit.app F.carrier

/-- Canonical finite-fibre exchange: pull back the direct-image counit and take its
adjunct for the finite structure map Z_0 to Spec(L). The two boundary identifications
are the published forgetful comparisons, and the middle square is a1FiniteFibreSquare.
Its degree-zero point fibre is b_y. Since Z_0 is finite, its proper direct image represents
RΓ_c(Z,G), and the target Weil structure represents F_(Z/L).
Source: Stacks 03QP(1)--(2), Weil II (1.1.7)--(1.1.10)
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1FiniteFibreBaseChange (F : sfCommonStageWeilComplex D l hl X₀ Ω) :
    (a1FiniteFibreStalkPair D g₀ y ι hι l hl Ω F).carrier ⟶
      ((sfModelWeilDerivedPush (a1ResidueDatum D Y₀ y ι hι) l hl Ω
        (a1FiniteFibreStructure D g₀ y ι hι)).obj
          (a1FiniteFibreWeilComplex D g₀ y ι hι l hl Ω F)).carrier :=
  let B := a1ResidueDatum D Y₀ y ι hι
  let a := a1FiniteFibreStructure D g₀ y ι hι
  let i := a1FiniteFibreInclusion D g₀ y ι hι
  let t := a1FiniteFibrePointInclusion D y ι hι
  let P := (sfModelWeilDerivedPush D l hl Ω g₀).obj F
  let G := a1FiniteFibreWeilComplex D g₀ y ι hι l hl Ω F
  letI := sfWeilPrimeInvertible B l hl (a1FiniteFibreModel D g₀ y)
  letI := sfWeilPrimeInvertible B l hl (sfWeilCohomologyPoint B)
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl Y₀
  (sfModelDerivedAdjunction B l hl Ω a).homEquiv _ _
    (((zlPullComp l Ω (zlFiberMap B a) t).app P.carrier).inv ≫
      eqToHom (congrArg (fun f ↦ (commonStageDerivedPullback l Ω f).obj P.carrier)
        (a1FiniteFibreSquare D g₀ y ι hι)) ≫
      ((zlPullComp l Ω i (zlFiberMap D g₀)).app P.carrier).hom ≫
      (commonStageDerivedPullback l Ω i).map (a1FiniteFibreCounit D g₀ l hl Ω F)) ≫
    (sfModelWeilDerivedPushForget B l hl Ω a).inv.app G

/-- Every closed point of the scheme-theoretic fibre maps to y.
Source: Stacks 03QP fibre (blueprint: lem-a1-finite-etale-weil-fibre-comparison).
Proof: evaluate pullback.condition at the point. Spec(kappa(y)) has one point,
whose image under fromSpecResidueField is y. -/
theorem a1FiniteFibrePoint_over
    (z : (a1FiniteFibreModel D g₀ y).left) :
    g₀.left (pullback.fst g₀.left (Y₀.left.fromSpecResidueField y.val) z) = y.val := by
  sorry

include hg in
/-- The image point is closed, including when the ambient source is not separated.
Source: Stacks 03QP fibre, closed-immersion residue-field invariance
(blueprint: lem-a1-finite-etale-weil-fibre-comparison).
Proof: the fibre inclusion is a closed immersion. Its residue field is unchanged
and finite over L, hence over k_0. The closed-point-field criterion makes its image
closed in X_0. -/
theorem a1FiniteFibreClosedImage_mem
    (z : {z : (a1FiniteFibreModel D g₀ y).left //
      z ∈ closedPoints (a1FiniteFibreModel D g₀ y).left}) :
    pullback.fst g₀.left (Y₀.left.fromSpecResidueField y.val) z.val ∈
      closedPoints X₀.left := by
  sorry

/-- The corresponding closed point of X_0, with the actual first-projection image.
Source: Stacks 03QP fibre (blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1FiniteFibreClosedImage
    (z : {z : (a1FiniteFibreModel D g₀ y).left //
      z ∈ closedPoints (a1FiniteFibreModel D g₀ y).left}) :
    {x : X₀.left // x ∈ closedPoints X₀.left} :=
  ⟨pullback.fst g₀.left (Y₀.left.fromSpecResidueField y.val) z.val,
    a1FiniteFibreClosedImage_mem D g₀ y z⟩

/-- The point correspondence, without a surjectivity assumption on g_0.
Source: Stacks 03QP fibre (blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1FiniteFibreClosedPointMap
    (z : {z : (a1FiniteFibreModel D g₀ y).left //
      z ∈ closedPoints (a1FiniteFibreModel D g₀ y).left}) :
    {x : X₀.left // g₀.left x = y.val} :=
  ⟨(a1FiniteFibreClosedImage D g₀ y z).val, a1FiniteFibrePoint_over D g₀ y z.val⟩

/-- Restriction to the finite fibre stays in the constructible heart.
Source: BS 6.8.11(3), 6.8.15; Stacks 03QP fibre
(blueprint: lem-a1-finite-etale-weil-fibre-comparison).
Proof: integral pullback preserves constructibility and its finite reductions are
ordinary exact inverse images. It is t-exact after localization and at common stages.
Its prescribed Weil map is an isomorphism, so the restricted pair is a Weil sheaf. -/
theorem a1FiniteFibreWeilComplex_mem (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    sfCommonStageHeartProperty l
      ((a1ResidueDatum D Y₀ y ι hι).geometricFiber (a1FiniteFibreModel D g₀ y)).left Ω
        (a1FiniteFibreWeilComplex D g₀ y ι hι l hl Ω F.obj).carrier := by
  sorry

/-- G as an object of the existing constructible Weil heart, with its actual restriction data.
Source: Stacks 03QP fibre and Weil II (1.1.7)--(1.1.10)
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1FiniteFibreWeilSheaf (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    sfCommonStageWeilSheaf (a1ResidueDatum D Y₀ y ι hι) l hl
      (a1FiniteFibreModel D g₀ y) Ω :=
  ⟨a1FiniteFibreWeilComplex D g₀ y ι hι l hl Ω F.obj,
    a1FiniteFibreWeilComplex_mem D g₀ y ι hι l hl Ω F⟩

/-- The absolute return at a fibre point uses [kappa(x):k_0], not [kappa(x):L].
Source: Weil II (1.1.7)--(1.1.10), residue-degree tower formula
(blueprint: lem-a1-finite-etale-weil-fibre-comparison).
Proof: the fibre closed immersion identifies kappa(z) with kappa(x) over L.
The tower formula is deg(x)=deg_L(z)*d_y. The geometric lift therefore returns under
gamma^deg(x). Pullback uniqueness gives the displayed semilinear return equality. -/
theorem a1FiniteFibreLocalReturn
    (z : {z : (a1FiniteFibreModel D g₀ y).left //
      z ∈ closedPoints (a1FiniteFibreModel D g₀ y).left})
    (rho : (a1FiniteFibreModel D g₀ y).left.residueField z.val →+* D.k)
    (hrho : rho.comp ((a1FiniteFibreModel D g₀ y).hom.residueFieldAlgebraMap z.val) = ι) :
    (localClosedPoint (a1ResidueDatum D Y₀ y ι hι) (a1FiniteFibreModel D g₀ y) z rho hrho ≫
        a1FiniteFibreInclusion D g₀ y ι hι) ≫
          localPositivePower (D.geometricFrobenius X₀).hom
            (localClosedPointDegree D X₀ (a1FiniteFibreClosedImage D g₀ y z) - 1) =
      localPositivePower (frobeniusPointIso D).hom
          (localClosedPointDegree D X₀ (a1FiniteFibreClosedImage D g₀ y z) - 1) ≫
        (localClosedPoint (a1ResidueDatum D Y₀ y ι hι) (a1FiniteFibreModel D g₀ y) z rho hrho ≫
          a1FiniteFibreInclusion D g₀ y ι hι) := by
  sorry

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The finite-stage fibre restriction, for local operator comparisons at a common field.
Source: Weil II (1.1.3), (1.1.7)--(1.1.10)
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1FiniteFibreRationalWeilComplex (K : sfWeilComplex D l hl X₀ E) :=
  a1ResidueRationalWeilComplex D Y₀ y ι hι (a1FiniteFibreModel D g₀ y) X₀
    (pullback.fst g₀.left (Y₀.left.fromSpecResidueField y.val))
    (a1FiniteFibreProjection_over D g₀ y) l hl E K

/-- The stalk restriction isomorphism, as H^0 of the prescribed pullback compositor.
Source: Stacks 03QP fibre and Weil II (1.1.7)--(1.1.10)
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1FiniteFibreRationalStalkIso (K : sfWeilComplex D l hl X₀ E)
    (z : {z : (a1FiniteFibreModel D g₀ y).left //
      z ∈ closedPoints (a1FiniteFibreModel D g₀ y).left})
    (rho : (a1FiniteFibreModel D g₀ y).left.residueField z.val →+* D.k)
    (hrho : rho.comp ((a1FiniteFibreModel D g₀ y).hom.residueFieldAlgebraMap z.val) = ι) :=
  (DerivedCategory.coefficientFdCohomology E 0).mapIso
    (a1ResidueRationalStalkComparison D Y₀ y ι hι (a1FiniteFibreModel D g₀ y) X₀
      (pullback.fst g₀.left (Y₀.left.fromSpecResidueField y.val))
      (a1FiniteFibreProjection_over D g₀ y) l hl E K
      (localClosedPoint (a1ResidueDatum D Y₀ y ι hι) (a1FiniteFibreModel D g₀ y) z rho hrho))

/-- Local Frobenius on G at z, followed by the canonical stalk restriction, is the
original F_x on F. Every finite-stage presentation and every compatible geometric lift
is included; no Frobenius-stable integral lattice is required.
Source: Weil II (1.1.7)--(1.1.10)
(blueprint: lem-a1-finite-etale-weil-fibre-comparison).
Proof: identify residue fields by the closed immersion and write deg(x)=deg_L(z)*d_y.
Expand the iterated structure of G: its deg_L(z) blocks each consist of d_y factors
of theta. The point transports likewise form the same deg(x) ordered one-step string.
Associativity of the integral pullback compositors and point-transport naturality
remove the different parentheses. Applying H^0 gives exactly the displayed equality.
Scalar extension preserves this equality at every common coefficient stage. -/
theorem a1FiniteFibreLocalFrobenius (ψ : E →+* Ω) (K : sfWeilComplex D l hl X₀ E)
    (z : {z : (a1FiniteFibreModel D g₀ y).left //
      z ∈ closedPoints (a1FiniteFibreModel D g₀ y).left})
    (rho : (a1FiniteFibreModel D g₀ y).left.residueField z.val →+* D.k)
    (hrho : rho.comp ((a1FiniteFibreModel D g₀ y).hom.residueFieldAlgebraMap z.val) = ι) :
    (ModuleCat.extendScalars ψ).map
      (localClosedFrobeniusCohomology l E (a1ResidueDatum D Y₀ y ι hι) hl
        (a1FiniteFibreModel D g₀ y) (a1FiniteFibreRationalWeilComplex D g₀ y ι hι l hl E K)
        z rho hrho 0 ≫ (a1FiniteFibreRationalStalkIso D g₀ y ι hι l hl E K z rho hrho).hom) =
      (ModuleCat.extendScalars ψ).map
        ((a1FiniteFibreRationalStalkIso D g₀ y ι hι l hl E K z rho hrho).hom ≫
        localFrobeniusCohomology l E D hl X₀ K
          (localClosedPoint (a1ResidueDatum D Y₀ y ι hι) (a1FiniteFibreModel D g₀ y) z rho hrho ≫
            a1FiniteFibreInclusion D g₀ y ι hι)
          (localClosedPointDegree D X₀ (a1FiniteFibreClosedImage D g₀ y z) - 1)
          (a1FiniteFibreLocalReturn D g₀ y ι hι z rho hrho) 0) := by
  sorry

include hg in
/-- Finite etale image is concentrated in degree zero and has the induced Weil structure.
The statement also covers an empty target, since it has no closed-point binder.
Source: Stacks 03QP(1)--(2), BS 6.8.14--6.8.15
(blueprint: lem-a1-finite-etale-weil-fibre-comparison).
Proof: split a finite etale map locally into finitely many sheets, including zero sheets.
Finite products of exact sheet restrictions are exact and preserve constructibility.
They commute with coefficient reduction. Normalized DVR tower effectivity reconstructs
the integral image in the same interval. Rational localization and common-stage descent
therefore preserve the heart. Frobenius acts by the mate of the normalized pullback
square followed by the image of theta, exactly sfModelWeilDerivedPush. Affine opens of
Y_0 base-changed to k give a Frobenius-stable finite cover, so no separatedness is needed. -/
theorem a1FiniteEtaleWeilImage_mem [Etale g₀.left]
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Ω
      (((sfModelWeilDerivedPush D l hl Ω g₀).obj F.obj).carrier) := by
  sorry

/-- Degree-zero point realization at an actual finite coefficient stage, followed by
extension to the specified algebraic closure. This uses the recorded rational fibre,
not a second stalk construction. Site and coefficient universes remain independent.
Source: Weil II (1.1.3), (1.1.7)--(1.1.10)
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
def a1PointLinearRealization (B : FiniteFieldDatum.{u}) (hB : l ≠ B.p)
    (T : Over (Spec (.of B.k₀))) [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    (S : AlgebraicallyClosedCoefficients.Index l Ω)
    (s : Spec (.of B.k) ⟶ (B.geometricFiber T).left) :=
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω S
  letI := sfWeilPrimeInvertible B l hB T
  letI : Fact (l ≠ B.p) := ⟨hB⟩
  letI := frobeniusPointPrimeInvertible B l hB
  rationalDerivedPullback l E s ⋙ pointRationalFibre B l hB E ⋙
    DerivedCategory.coefficientFdCohomology E 0 ⋙
      ModuleCat.extendScalars (sfAdicCoefficientEmbedding l Ω S)

include hg in
/-- The canonical comparison and both Weil objects admit simultaneous finite-stage
coordinates. The last equality fixes the arrow to the actual counit mate, followed by
the proper compact/ordinary identification in the chosen compact presentation.
There is no freely chosen vector-space isomorphism in the conclusion's input.
Source: Weil II (1.1.3); Stacks 03QP; blueprint proof, Steps 7--10
(blueprint: lem-a1-finite-etale-weil-fibre-comparison).
Proof: the finite-fibre mate is an equivariant isomorphism by Steps 1--8. Proper
coincidence identifies its target with the recorded compact cohomology Weil object.
The category is the filtered colimit of the finite coefficient categories. Descend
both objects, their structure isomorphisms and inverses, the comparison and its
commutation identity to one common stage. The filtered-colimit hom relation gives
exactly the displayed equality after inclusion. No rationality or semisimplicity
condition on the Weil automorphism is used. -/
theorem a1FiniteFibreStageCoordinates [Etale g₀.left]
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    ∃ S : AlgebraicallyClosedCoefficients.Index l Ω,
      ∃ K L : sfWeilComplex (a1ResidueDatum D Y₀ y ι hι) l hl (sfWeilCohomologyPoint (a1ResidueDatum
        D Y₀ y ι hι))
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω S),
        ∃ α : sfWeilStageObject (a1ResidueDatum D Y₀ y ι hι) l hl (sfWeilCohomologyPoint
          (a1ResidueDatum D Y₀ y ι hι)) Ω S K ≅
          a1FiniteFibreStalkPair D g₀ y ι hι l hl Ω F.obj,
        ∃ β : sfWeilStageObject (a1ResidueDatum D Y₀ y ι hι) l hl (sfWeilCohomologyPoint
          (a1ResidueDatum D Y₀ y ι hι)) Ω S L ≅ (commonStageCompactWeilCohomology (a1ResidueDatum D
          Y₀ y ι hι) l hl Ω
          (a1FiniteFibreModel D g₀ y)
          (Compactification.ofIsProper (a1FiniteFibreModel D g₀ y).hom)
          (a1FiniteFibreWeilSheaf D g₀ y ι hι l hl Ω F) 0).obj,
        ∃ c : ((sfModelWeilDerivedPush (a1ResidueDatum D Y₀ y ι hι) l hl Ω
          (a1FiniteFibreStructure D g₀ y ι hι)).obj
            (a1FiniteFibreWeilComplex D g₀ y ι hι l hl Ω F.obj)) ≅ (commonStageCompactWeilCohomology
              (a1ResidueDatum D Y₀ y ι hι) l hl Ω
          (a1FiniteFibreModel D g₀ y)
          (Compactification.ofIsProper (a1FiniteFibreModel D g₀ y).hom)
          (a1FiniteFibreWeilSheaf D g₀ y ι hι l hl Ω F) 0).obj,
        ∃ f : K ⟶ L,
          (GeneralAlgebraicallyClosedCoefficients.inclusion S).map f.hom.f =
            α.hom.hom.f ≫ a1FiniteFibreBaseChange D g₀ y ι hι l hl Ω F.obj ≫
              c.hom.hom.f ≫ β.inv.hom.f := by
  sorry

include hg in
/-- In every simultaneous finite-stage presentation of the canonical mate, taking
H⁰ of the geometric point and extending scalars gives the actual Ω-linear isomorphism
and the equality b_y F_y = F_(Z/L) b_y. The target presentation is the recorded H_c⁰
Weil object; c is a proper identification, never a replacement for the canonical mate.
Source: Weil II (1.1.3), (1.1.7)--(1.1.10); blueprint proof, Steps 7--10
(blueprint: lem-a1-finite-etale-weil-fibre-comparison).
Proof: α, β and c transport the isomorphism assertion for the canonical mate.
A finite-stage arrow whose algebraic-closure inclusion is invertible becomes
invertible after extension of scalars. Apply the exact degree-zero point fibre.
Since f is a map of the actual Weil pairs, its square with their structure maps
commutes. The point-transport naturality identity moves that square through the
specified local return and reparametrization. Degree zero and extension to Ω
preserve the equality. On Spec(L) this local degree-one operator is precisely
F_y on the source and global relative-L Frobenius on compact cohomology. -/
theorem a1FiniteFibreLinearComparison [Etale g₀.left]
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω)
    (S : AlgebraicallyClosedCoefficients.Index l Ω)
    (K L : sfWeilComplex (a1ResidueDatum D Y₀ y ι hι) l hl
      (sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι))
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω S))
    (α : sfWeilStageObject (a1ResidueDatum D Y₀ y ι hι) l hl
      (sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι)) Ω S K ≅
        a1FiniteFibreStalkPair D g₀ y ι hι l hl Ω F.obj)
    (β : sfWeilStageObject (a1ResidueDatum D Y₀ y ι hι) l hl
      (sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι)) Ω S L ≅
        (commonStageCompactWeilCohomology (a1ResidueDatum D Y₀ y ι hι) l hl Ω
          (a1FiniteFibreModel D g₀ y)
          (Compactification.ofIsProper (a1FiniteFibreModel D g₀ y).hom)
          (a1FiniteFibreWeilSheaf D g₀ y ι hι l hl Ω F) 0).obj)
    (c : ((sfModelWeilDerivedPush (a1ResidueDatum D Y₀ y ι hι) l hl Ω
      (a1FiniteFibreStructure D g₀ y ι hι)).obj
        (a1FiniteFibreWeilComplex D g₀ y ι hι l hl Ω F.obj)) ≅
      (commonStageCompactWeilCohomology (a1ResidueDatum D Y₀ y ι hι) l hl Ω
        (a1FiniteFibreModel D g₀ y)
        (Compactification.ofIsProper (a1FiniteFibreModel D g₀ y).hom)
        (a1FiniteFibreWeilSheaf D g₀ y ι hι l hl Ω F) 0).obj)
    (f : K ⟶ L)
    (hf : (GeneralAlgebraicallyClosedCoefficients.inclusion S).map f.hom.f =
      α.hom.hom.f ≫ a1FiniteFibreBaseChange D g₀ y ι hι l hl Ω F.obj ≫
        c.hom.hom.f ≫ β.inv.hom.f)
    (s₀ : {s : (sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι)).left //
      s ∈ closedPoints (sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι)).left})
    (eta : (sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι)).left.residueField s₀.val
      →+* D.k)
    (heta : eta.comp
      ((sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι)).hom.residueFieldAlgebraMap
        s₀.val) = @algebraMap (a1ResidueDatum D Y₀ y ι hι).k₀ D.k _ _
          (a1ResidueDatum D Y₀ y ι hι).algebra_closure) :
    IsIso ((a1PointLinearRealization l Ω (a1ResidueDatum D Y₀ y ι hι) hl
          (sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι)) S
          (localClosedPoint (a1ResidueDatum D Y₀ y ι hι)
            (sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι)) s₀ eta heta)).map f.hom.f) ∧
      (ModuleCat.extendScalars (sfAdicCoefficientEmbedding l Ω S)).map
        (localClosedFrobeniusCohomology l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω S)
          (a1ResidueDatum D Y₀ y ι hι) hl (sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι)) K s₀
            eta heta 0) ≫ (a1PointLinearRealization l Ω (a1ResidueDatum D Y₀ y ι hι) hl
          (sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι)) S
          (localClosedPoint (a1ResidueDatum D Y₀ y ι hι)
            (sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι)) s₀ eta heta)).map f.hom.f =
        (a1PointLinearRealization l Ω (a1ResidueDatum D Y₀ y ι hι) hl
          (sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι)) S
          (localClosedPoint (a1ResidueDatum D Y₀ y ι hι)
            (sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι)) s₀ eta heta)).map f.hom.f ≫
              (ModuleCat.extendScalars (sfAdicCoefficientEmbedding l Ω S)).map
              (localClosedFrobeniusCohomology l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω S)
            (a1ResidueDatum D Y₀ y ι hι) hl (sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι)) L
              s₀ eta heta 0) := by
  sorry

include hg in
/-- Finite-fibre comparison with its actual relative-L Weil action and residue fields.
The canonical counit mate represents b_y after taking the degree-zero point fibre.
Its displayed Weil square is precisely b_y F_y = F_(Z/L) b_y in that representation.
The proper target is also represented by the recorded compact-support cohomology;
the isomorphism below is in Weil pairs, so it retains that operator.
The separate a1FiniteFibreLocalFrobenius clause states the local restriction equality
at every finite coefficient field and every geometric lift.
Source: Stacks 03QP; Weil II (1.1.3), (1.1.7)--(1.1.10); main-20261015,
lem-a1-finite-map-purity.proof.md, first paragraph
(blueprint: lem-a1-finite-etale-weil-fibre-comparison).

Proof:
1. First work at finite coefficients $A_n=\mathcal O_E/\varpi_E^n$. A finite etale map is
etale-locally a finite disjoint union of identity maps, including the empty union
[lem-weil-pbc-finite-etale-etale-local-split]. On such a neighborhood its pro-etale direct image
is the finite product of the restrictions to the sheets: evaluation on $T\to U$ gives the product
of sections on the copies of $T$. Restriction to these etale neighborhoods is exact and preserves
injectives [lem-weil-pbc-proetale-restriction-injectives], so the same calculation computes the
derived image of a bounded complex. Thus it is exact and preserves its cohomological interval. The
finite products commute with derived change $A_m\to A_n$ (finite products are finite sums, and
tensor is additive); consequently the canonical coefficient-exchange maps for this direct image
are isomorphisms. These identities glue, since their maps are the restriction and coefficient maps
themselves. For constructibility, represent a finite-level constructible pro-etale complex by its
etale antecedent [lem-sf-proetale-constructible-origin]. The sheaf comparison $\nu_Y^*g_*\to
g_*\nu_X^*$ is the identity on every sheet in the preceding calculation, hence is an isomorphism.
The etale direct image is exact and constructible by [fin4-thm-finite-morphisms-constructible].
This proves finite-level constructibility on $Y$ without assuming $X$ or $Y$ separated.
2. Let $K$ be an integral constructible complex representing an object at coefficient field $E$.
Its reductions $K_n$ are constructible in a single interval $[a,b]$, by
[def-weil-derived-complete-integral-detailed]. By Step 1 the tower $M_n=Rg_*K_n$ is constructible
in that same interval, and its canonical quotient comparisons $M_m\otimes^L_{A_m}A_n\to M_n$ are
isomorphisms. Apply the direct image to the strict coefficient tower representing $K$; this
supplies the coherent tower and quotient cocycle, not merely an inverse system in a homotopy
category. Thus it is a normalized tower in the sense of [def-coef-normalized-dvr-tower]. The
effectivity theorem [lem-coef-normalized-dvr-effectivity] identifies every reduction of
$M=R\varprojlim_n\operatorname{Res}_nM_n$ with $M_n$ and makes $M$ derived complete. Together with
the already proved constructibility and uniform interval this is exactly membership in the
integral category. This $M$ is the integral $Rg_*K$ of [def-weil-derived-direct-image]. Localizing
scalars therefore gives $Rg_*$ on the required rational constructible category. No finite-Tor
bound on the reductions was used.
3. Choose a finite affine open cover $U_{i,0}$ of $Y_0$ and put $U_i=U_{i,0}\times_{k_0}k$: these
are affine opens covering $Y$, stable under the base-field Frobenius
$\operatorname{id}_{Y_0}\times\operatorname{Spec}(\gamma)$. Their inverse images $V_i$ are affine
since $g$ is finite [lem-weil-pbc-finite-morphism-permanence]; these are separated finite-type
$k$-schemes. Finite-level open restriction commutes with derived image
[lem-exc-proetale-derived-open-restriction]. It also commutes with the derived limit defining the
integral image: ringed-site open restriction is exact with exact left adjoint extension by zero
[lem-pur-site-restriction-module-adjunction-exact], hence preserves injectives and limits, also on
towers. Completed restriction is the same restriction [lem-sf-pf-open-factor-coherence](1). These
comparisons pass to rational localization. Consequently $(Rg_*\mathcal
F)|_{U_i}=R(g|_{V_i})_*(\mathcal F|_{V_i})$. Apply [lem-zl-finite-adic-direct-image] to each
$V_i\to U_i$: this lies in degree zero. This is a local assertion for the standard constructible
t-structure [prop-constructible-truncations]; its sheaf interpretation and checking on separated
open covers are [lem-dl-a1-constructible-fibres-exact]. Explicitly, at an integral representative
each cohomology sheaf outside degree zero is killed locally by a power of $\varpi_E$; a finite
cover gives a single power, so it vanishes after rational localization. Hence $Rg_*\mathcal F$ is
in the constructible heart. The same local finite-adic lemma supplies the canonical
stalk-to-fibre-sections isomorphism, natural also for semilinear isomorphisms of diagrams. It is
independent of the affine neighborhood because all its arrows are restriction maps.
4. Write $\phi_X,\phi_Y$ for the geometric base-field Frobenius automorphisms, to distinguish them
from $g$. The finite morphism $g_0$ is proper and in particular separated
[lem-weil-pbc-finite-proper]. Steps 1--3 have verified the bounded-constructibility domain;
therefore [lem-fix-weil-operations] applies. If $\theta:\phi_X^*\mathcal F\to\mathcal F$ is its
Weil structure, the induced structure on the degree-zero image is $\phi_Y^*g_*\mathcal
F\xrightarrow{\mathrm{Ex}}g_*\phi_X^*\mathcal F\xrightarrow{g_*\theta}g_*\mathcal F$. Its iterates
use the iterated exchanges and $\theta^{[n]}$. The composition comparisons and exchanges are
equivariant by the same cited lemma. This proves the claimed induced Weil structure, having
established constructibility separately rather than inferring it from equivariance.
5. The field $L=\kappa(y)$ has finite degree $d_y$ over $k_0$ by [lem-kun-closed-point-field](a).
Base change of a finite morphism is finite [lem-weil-pbc-finite-morphism-permanence], so $Z_0$ is
finite over $L$ and proper [lem-weil-pbc-finite-proper]. The map $Z_0\to X_0$ is the base change
of the closed immersion $\operatorname{Spec}L\to Y_0$, and hence is a closed immersion
[lem-weil-pbc-closed-immersion-base-change]. In an affine neighborhood of $y$, write
$Y_0=\operatorname{Spec}A$ and its finite inverse image as $\operatorname{Spec}B$. Then
$Z_0=\operatorname{Spec}(B\otimes_A\kappa(y))$. Prime ideals in this quotient correspond exactly
to primes of $B$ over the maximal ideal of $y$. Their residue fields are unchanged, also as
$L$-fields [lem-weil-pbc-closed-immersion-residue-field-iso]. Each is finite over $L$: the
corresponding quotient of the finite-dimensional $L$-algebra is a finite-dimensional domain and
hence a field, since multiplication by any nonzero element is injective and therefore surjective.
Thus these $x$ are closed also in $X_0$ by [lem-kun-closed-point-field](a). This proves the point
correspondence and all residue-field assertions, without a surjectivity assumption.
6. Let $i:Z\to X$ be the fibre inclusion with the chosen embedding $L\hookrightarrow k$. The
pullback $i^*\mathcal F$ is constructible: integral pullback preserves constructibility and
reduces to ordinary inverse image [lem-pur-integral-operations-preserve-constructible](1). It lies
in the constructible heart, because pullback along the morphism $i$ of finite-type $k$-schemes is
$t$-exact and commutes with $\mathcal H^j$ [lem-a1-constructible-pullback-t-exact]. By the same
lemma and pullback composition its geometric fibres are those of $\mathcal F$, which on the
separated affine charts $V_i$ of Step 3 are the exact fibre functors of
[lem-dl-a1-constructible-fibres-exact]. Put
$\psi_Z=\operatorname{id}_{Z_0}\times\operatorname{Spec}(\gamma^{d_y})$, the base-field Frobenius
for $L$. Since $\gamma^{d_y}$ fixes $L$, $i\psi_Z=\phi_X^{d_y}i$. Pull back $\theta^{[d_y]}$ along
$i$ and use this equality to define $\eta:\psi_Z^*i^*\mathcal F\xrightarrow{\sim}i^*\mathcal F$.
Iterates and reparametrizations are precisely those of [def-weil-local-frobenius-trace], with the
associative pullback comparisons [lem-pod-integral-pullback-composition], localized at $E$. This
gives the asserted Weil sheaf $\mathcal G=(i^*\mathcal F,\eta)$ on $Z_0/L$.
7. Let $a_y:(g_*\mathcal F)_{\bar y}\to H^0(Z,i^*\mathcal F)$ be the restriction isomorphism from
Step 3 and [lem-zl-finite-adic-direct-image]. Since $Z_0/L$ is proper,
[lem-pod-proper-coincidence-frobenius] gives a natural isomorphism $c:H_c^0(Z,i^*\mathcal F)\to
H^0(Z,i^*\mathcal F)$ compatible with Frobenius transport. Define $b_y=c^{-1}a_y$. This is the
usual finite-fibre base-change map followed by proper compact/ordinary identification. It remains
to check its operator, rather than only its underlying vector space.
8. On the chart $V_i\to U_i$ of Step 3 containing $\bar y$, which $\phi_X,\phi_Y$ preserve, apply
the semilinear diagram-naturality of [lem-zl-finite-adic-direct-image] to
$\phi_X^{d_y},\phi_Y^{d_y}$ and the point return $\phi_Y^{d_y}\bar y=\bar y\gamma_s^{d_y}$. It
identifies the transport of the source of $a_y$ with cohomology transport along $\psi_Z$ on its
target. Concretely every restriction to a geometric lift in the fibre is reindexed by
$\phi_X^{d_y}$ and has the induced point transport; these are the same restrictions on both
routes. Naturality for the sheaf morphism $\theta^{[d_y]}$ then identifies the subsequent source
action with $H^0(\eta)$. The point-transport naturality identity
[lem-weil-frobenius-point-transport-natural](2) permits exactly these restriction and structure
maps to pass through the transports. Thus the composite on the source is $F_y$ by
[def-weil-local-frobenius-trace], whereas the target composite is ordinary $L$-Frobenius by
[def-weil-global-geometric-frobenius]. The transports used here are the specified isomorphisms
[lem-weil-frobenius-cohomology-transport-iso], applied with finite base $L$. Hence
$a_yF_y=F_{Z/L}^{\mathrm{ord}}a_y$. Proper-coincidence transport compatibility
[lem-pod-proper-coincidence-frobenius](2), followed by naturality for $\eta$, gives
$cF_{Z/L}=F_{Z/L}^{\mathrm{ord}}c$. Combining the two equalities proves $b_yF_y=F_{Z/L}b_y$.
9. For a point $z_0$ corresponding to $x$ put $e=[\kappa(x):L]$. Step 5 identifies the fields, and
the elementary tower formula gives $[\kappa(x):k_0]=ed_y$. At a chosen geometric lift, pullback
composition identifies the stalk of $\mathcal G$ with that of $\mathcal F$. In the formula
[def-weil-local-frobenius-trace] for its local operator over $L$, the structure map is the
$e$-fold iterate of $\eta$. Expanding $\eta$ gives the same ordered string of $ed_y$ factors
$\theta$ as $\theta^{[ed_y]}$. The point transport is likewise the ordered string of $ed_y$
one-step transports, grouped into $e$ blocks of length $d_y$; the point reparametrization is
$\gamma_s^{ed_y}$ in either expression. Associativity of the specified pullback comparisons
[lem-pod-integral-pullback-composition] removes the parentheses, and naturality
[lem-weil-frobenius-point-transport-natural] identifies the intervening pullback maps. The two
composites are therefore identical, which proves that the relative-$L$ local operator is the
original $F_x$. This checks the operator itself, with its geometric-Frobenius convention, rather
than merely its trace or eigenvalues.
10. For $\Qlb$ choose a common finite extension $E/\mathbf Q_\ell$ representing $\mathcal F$, its
Weil isomorphism and inverse, and their inverse identities. Such a stage exists by
[def-weil-algebraically-closed-coefficients]. All constructions above commute with enlarging this
field: for the stalk formula this is part of [lem-zl-finite-adic-direct-image], and for point
transports it is part of [lem-weil-frobenius-point-transport-natural](2). All other arrows are
canonical coefficient-stage pullbacks, direct images and their comparisons already constructed at
that stage. Extend the equalities to $\Qlb$. Empty fibres give zero on both sides; degree-one
points give the one-step action; disconnected fibres require no choice of ordering. Nothing in the
argument uses purity, lissity or semisimplicity.
-/
theorem a1FiniteEtaleWeilFibreComparison [Etale g₀.left]
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Ω
      (((sfModelWeilDerivedPush D l hl Ω g₀).obj F.obj).carrier) ∧
      IsIso (a1FiniteFibreBaseChange D g₀ y ι hι l hl Ω F.obj) ∧
      ((sfCommonStageWeilFrobeniusPullback (a1ResidueDatum D Y₀ y ι hι) l hl
          (sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι)) Ω).map
            (a1FiniteFibreBaseChange D g₀ y ι hι l hl Ω F.obj) ≫
        ((sfModelWeilDerivedPush (a1ResidueDatum D Y₀ y ι hι) l hl Ω
          (a1FiniteFibreStructure D g₀ y ι hι)).obj
            (a1FiniteFibreWeilComplex D g₀ y ι hι l hl Ω F.obj)).str.hom =
        (a1FiniteFibreStalkPair D g₀ y ι hι l hl Ω F.obj).str.hom ≫
          a1FiniteFibreBaseChange D g₀ y ι hι l hl Ω F.obj) ∧
      sfCommonStageHeartProperty l
        ((a1ResidueDatum D Y₀ y ι hι).geometricFiber
          (sfWeilCohomologyPoint (a1ResidueDatum D Y₀ y ι hι))).left Ω
        (((sfModelWeilDerivedPush (a1ResidueDatum D Y₀ y ι hι) l hl Ω
          (a1FiniteFibreStructure D g₀ y ι hι)).obj
            (a1FiniteFibreWeilComplex D g₀ y ι hι l hl Ω F.obj)).carrier) ∧
      Nonempty (((sfModelWeilDerivedPush (a1ResidueDatum D Y₀ y ι hι) l hl Ω
          (a1FiniteFibreStructure D g₀ y ι hι)).obj
            (a1FiniteFibreWeilComplex D g₀ y ι hι l hl Ω F.obj)) ≅
        (commonStageCompactWeilCohomology (a1ResidueDatum D Y₀ y ι hι) l hl Ω
          (a1FiniteFibreModel D g₀ y)
          (Compactification.ofIsProper (a1FiniteFibreModel D g₀ y).hom)
          (a1FiniteFibreWeilSheaf D g₀ y ι hι l hl Ω F) 0).obj) ∧
      Function.Bijective (a1FiniteFibreClosedPointMap D g₀ y) ∧
      (∀ x : X₀.left, g₀.left x = y.val → x ∈ closedPoints X₀.left) ∧
      (∀ z : (a1FiniteFibreModel D g₀ y).left,
        IsIso ((pullback.fst g₀.left (Y₀.left.fromSpecResidueField y.val)).residueFieldMap z)) := by
  sorry

end WeilConjectures
