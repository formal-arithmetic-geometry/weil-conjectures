/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntegralPullbackComposition
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.ProperCoincidenceFrobenius
public import Sheaf.SixFunctors.FrobeniusCohomologyTransport
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
import Sheaf.Paper.FrobeniusGeometricExchange
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.Paper.CompletedRlimFunctor
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.SixFunctors.FrobeniusCohomologyTransportIso

/-! # Proper sections and semilinear derived germs

Source: Deligne, Weil II (1.1.7), (1.1.10)--(1.1.14), pp. 150--153;
Stacks 07A7 and 0D6D (blueprint: lem-a1-proper-sections-semilinear-germs).
The germs below use the actual whole-system adjunction counit. Composition maps
are the specified simultaneous-system comparisons, localized at the coefficient field.

## Main declarations

* `ProperSemilinearGerms.integralCounit`, `ProperSemilinearGerms.rationalGerm`: the actual
  counit and its compact rational germ.
* `ProperSemilinearGerms.rationalTransport`, `ProperSemilinearGerms.rationalSquare`: the
  specified positive iterates and moving-point comparison.
* `properSectionsSemilinearGermsRational`, `properSectionsSemilinearGerms`: the identity
  and its naturality over a finite extension and over the algebraic closure.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open FrobeniusExchange

set_option allowUnsafeReducibility true in
attribute [local reducible] FrobeniusExchange.modelFunctor
  FrobeniusExchange.modelRationalSource FrobeniusExchange.modelRationalTarget

namespace ProperSemilinearGerms

variable (D : FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of D.k₀))) [IsProper Y₀.hom]
  (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The fixed simultaneous coefficient system used by the recorded exchanges.
Source: Stacks 0941, 099N (blueprint: lem-a1-proper-sections-semilinear-germs). -/
abbrev comparisons :=
  (integralPullbackComparisonRealization l (ULift.{u} ℚ_[l]) (ULift.{u} ℚ_[l])
    (AlgHom.id ℚ_[l] (ULift.{u} ℚ_[l]))).choose

/-- The ordinary integral counit, obtained before evaluating any finite quotient.
It is pullback realization, the reconstruction counit, the system geometric
counit, and the inverse completeness unit, in that order.
Source: Stacks 07A7, 0941 (blueprint: lem-a1-proper-sections-semilinear-germs). -/
def integralCounit (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :
    (constructibleIntegralPullback l E (D.geometricFiber Y₀).hom).obj
      ((properFrobeniusIntegralFunctor D Y₀ l E false).obj M) ⟶ M :=
  let X := (D.geometricFiber Y₀).left
  let s := Spec (.of D.k)
  let a := (D.geometricFiber Y₀).hom
  let A := integralComparisonDerivedSequencePullback l E a
  let R := systemDirect l E a
  let B := reduction l E X
  let S := (models l E).system s
  let T := (models l E).system X
  letI := (models l E).complete X M
  ObjectProperty.homMk
    (((models l E).pullback a).realization.hom.app
        ((properFrobeniusIntegralFunctor D Y₀ l E false).obj M).obj ≫
      (coefficientSequenceLimit l E X).map
        (A.map (S.adjunction.counit.app (R.obj (B.obj M.obj))) ≫
          (systemAdjunction l E a).counit.app (B.obj M.obj)) ≫
      inv (T.adjunction.unit.app M.obj))

/-- The integral germ before applying the point fibre. The inverse identity
comparison and z*a*=id comparisons put the counit in the required coordinates.
Source: Stacks 07A7, 0D6D (blueprint: lem-a1-proper-sections-semilinear-germs). -/
def integralGerm
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :
    (properFrobeniusIntegralFunctor D Y₀ l E false).obj M ⟶
      (constructibleIntegralPullback l E z).obj M :=
  ObjectProperty.homMk
    ((integralComparisonUnit l E (comparisons l) (Spec (.of D.k))
        ((properFrobeniusIntegralFunctor D Y₀ l E false).obj M)).inv ≫
      eqToHom (congrArg (fun f ↦ (integralDerivedPullback l E f).obj
        ((properFrobeniusIntegralFunctor D Y₀ l E false).obj M).obj) hz.symm) ≫
      (((integralPullbackComposition l E).choose z
        (D.geometricFiber Y₀).hom).hom.app
        ((properFrobeniusIntegralFunctor D Y₀ l E false).obj M)).hom ≫
      (integralDerivedPullback l E z).map (integralCounit D Y₀ l E M).hom)

/-- The compact rational germ, using the identity-compactification comparison,
then the scalar-localized integral germ and the actual rational-pullback object map.
Source: Deligne (1.1.14); Stacks 07A7
(blueprint: lem-a1-proper-sections-semilinear-germs). -/
def rationalGerm
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  (pointRationalFibre D l Fact.out E).map
    ((properFrobeniusRationalIso D Y₀ l E).hom.app M ≫
      (sfRationalConstructibleLocalization l E (Spec (.of D.k))).map
        (integralGerm D Y₀ l E z hz M.obj) ≫
      (localPullbackObjectIso l E z M).inv)

/-- The compact-cohomology functor at the identity compactification, followed by Fib_s.
Source: Deligne (1.1.14) (blueprint: lem-a1-proper-sections-semilinear-germs). -/
abbrev rationalSections :=
  properFrobeniusRationalFunctor D Y₀ l E true ⋙ pointRationalFibre D l Fact.out E

/-- The actual derived fibre at a geometric k-point.
Source: Deligne (1.1.10) (blueprint: lem-a1-proper-sections-semilinear-germs). -/
abbrev rationalFibre (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  rationalDerivedPullback l E z ⋙ pointRationalFibre D l Fact.out E

/-- Compact transport iterated r+1 times, with the final inverse compositor.
This recursion is the uncontracted iterate followed by its canonical contraction.
Source: Deligne (1.1.14); Stacks 0D6D
(blueprint: lem-a1-proper-sections-semilinear-germs). -/
def rationalTransport
    (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :
    (r : ℕ) → (rationalSections D Y₀ l E).obj M ⟶
      (rationalSections D Y₀ l E).obj
        ((rationalDerivedPullback l E
          (localPositivePower (D.geometricFrobenius Y₀).hom r)).obj M)
  | 0 => (frobeniusCohomologyTransportRational D l Fact.out E Y₀
      (Compactification.ofIsProper Y₀.hom) M).2
  | r + 1 =>
    (frobeniusCohomologyTransportRational D l Fact.out E Y₀
        (Compactification.ofIsProper Y₀.hom) M).2 ≫
      rationalTransport ((rationalDerivedPullback l E (D.geometricFrobenius Y₀).hom).obj M) r ≫
      (rationalSections D Y₀ l E).map
        (localPullbackComposition l E
          (localPositivePower (D.geometricFrobenius Y₀).hom r)
          (D.geometricFrobenius Y₀).hom M).inv

/-- The reparametrized point g^(r+1) z h^(-(r+1)), in composition order.
Source: Deligne (1.1.7), (1.1.10)
(blueprint: lem-a1-proper-sections-semilinear-germs). -/
def movingPoint (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (r : ℕ) :=
  localPositivePower (frobeniusPointIso D).inv r ≫ z ≫
    localPositivePower (D.geometricFrobenius Y₀).hom r

/-- Moving points remain k-points and give the displayed semilinear square.
Source: Deligne (1.1.7); Stacks 0D6D
(blueprint: lem-a1-proper-sections-semilinear-germs).
Proof: the defining projection equation g a = a h iterates to g^m a = a h^m.
Compose with h^(-m) z and use z a = id to obtain the first equality. Cancel
h^m h^(-m) in the definition of the moving point to obtain the second equality.
The recurrence localPositivePower denotes exponent m=r+1. -/
theorem movingPoint_properties
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (r : ℕ) :
    movingPoint D Y₀ z r ≫ (D.geometricFiber Y₀).hom = 𝟙 _ ∧
      localPositivePower (frobeniusPointIso D).hom r ≫ movingPoint D Y₀ z r =
        z ≫ localPositivePower (D.geometricFrobenius Y₀).hom r := by
  sorry

/-- b_(r+1,z,M) from the two canonical compositors and the actual square equality.
Source: Deligne (1.1.14); Stacks 0D6D
(blueprint: lem-a1-proper-sections-semilinear-germs). -/
def rationalSquare
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (r : ℕ)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  (localPullbackComposition l E (localPositivePower (frobeniusPointIso D).hom r)
      (movingPoint D Y₀ z r) M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (rationalDerivedPullback l E f).obj M)
      (movingPoint_properties D Y₀ z hz r).2) ≪≫
    localPullbackComposition l E z
      (localPositivePower (D.geometricFrobenius Y₀).hom r) M

/-- Left side of the derived germ equation, with its specified compact transport.
Source: Deligne (1.1.14) (blueprint: lem-a1-proper-sections-semilinear-germs). -/
def rationalLeft
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (r : ℕ)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  rationalTransport D Y₀ l E M r ≫
    rationalGerm D Y₀ l E z hz
      ((rationalDerivedPullback l E
        (localPositivePower (D.geometricFrobenius Y₀).hom r)).obj M)

/-- Right side: germ at the moving point, successive specified point transports,
then Fib_s(b). All positive exponents are represented by r+1.
Source: Deligne (1.1.10)--(1.1.14)
(blueprint: lem-a1-proper-sections-semilinear-germs). -/
def rationalRight
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (r : ℕ)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  rationalGerm D Y₀ l E (movingPoint D Y₀ z r)
      (movingPoint_properties D Y₀ z hz r).1 M ≫
    localPointTransportIterate l E D Fact.out
      ((rationalDerivedPullback l E (movingPoint D Y₀ z r)).obj M) r ≫
    (pointRationalFibre D l Fact.out E).map (rationalSquare D Y₀ l E z hz r M).hom

variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Faithful derived realization of a finite-dimensional complex at a common
coefficient stage. This is the very coefficient transport used by the recorded
cohomology transport; its ULift maps retain independent coefficient universes.
Source: Deligne (1.1.14); common-stage coefficient convention
(blueprint: lem-a1-proper-sections-semilinear-germs). -/
abbrev stageRealization (F : AlgebraicallyClosedCoefficients.Index l Ω) :=
  (DerivedCategory.pointFiniteDimensional
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).ι ⋙
    frobeniusCohomologyCoefficientExtension.{u, v}
      (F.val.subtype.comp (Shrink.algEquiv ℚ_[l] F.val).toRingHom)

/-- The left composite with algebraically closed coefficients, represented at
M's actual finite coefficient stage and then faithfully realized in D(Ω).
Source: Deligne (1.1.14); common-stage convention
(blueprint: lem-a1-proper-sections-semilinear-germs). -/
def qbarLeft
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (r : ℕ)
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :=
  (stageRealization l Ω M.stage).map
    (rationalLeft D Y₀ l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω M.stage)
      z hz r M.obj)

/-- The right composite at M's same finite stage. The rational formula supplies
exactly the germ, iterated restriction/insertion/kappa, and Fib_s(b); hence this
is their common-stage class, using no Weil structure on M.
Source: Deligne (1.1.10)--(1.1.14); common-stage convention
(blueprint: lem-a1-proper-sections-semilinear-germs). -/
def qbarRight
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (r : ℕ)
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :=
  (stageRealization l Ω M.stage).map
    (rationalRight D Y₀ l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω M.stage)
      z hz r M.obj)

/-- The canonical realized point-fibre comparison to any larger coefficient stage.
It is the balanced tensor tower, the normalized point-fibre scalar comparison,
and the identification of the recorded stage transition, in that order.
Source: Deligne (1.1.10)--(1.1.14), coefficient extension
(blueprint: lem-a1-proper-sections-semilinear-germs). -/
def realizedPointComparison
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : P.stage ≤ L) :
    (stageRealization l Ω P.stage).obj
        ((pointRationalFibre D l Fact.out
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)).obj P.obj) ≅
      (stageRealization l Ω L).obj
        ((pointRationalFibre D l Fact.out
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).obj (P.toStage h)) :=
  eqToIso (congrArg
      (fun φ ↦ (frobeniusCohomologyCoefficientExtension φ).obj
        ((pointRationalFibre D l Fact.out
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)).obj P.obj).obj)
      (frobeniusCohomologyStageEmbedding_comp l Ω P.stage L h).symm) ≪≫
    (frobeniusCoefficientTower
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω P.stage L h).toRingHom
      (frobeniusCohomologyStageEmbedding.{u, v} l Ω L)).symm.app _ ≪≫
    (stageRealization l Ω L).mapIso
      ((pointRationalFibreScalarIso D l Fact.out
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
        (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω P.stage L h)).symm.app
          P.obj) ≪≫
    (stageRealization l Ω L).mapIso
      ((pointRationalFibre D l Fact.out
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).mapIso
          ((operationStageTransitionIso l Ω (Spec (.of D.k)) P.stage L h).symm.app P.obj))

/-- The canonical realized comparison for the target C_z(P_(r+1) M).
Use the point-fibre coefficient comparison, then the recorded pullback scalar
comparisons for z and g^(r+1), retaining their stage-transition identifications.
Source: Deligne (1.1.10)--(1.1.14); Stacks 0D6D
(blueprint: lem-a1-proper-sections-semilinear-germs). -/
def realizedTargetComparison
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (r : ℕ)
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : M.stage ≤ L) :=
  let P := commonStagePullbackObject l Ω
    (localPositivePower (D.geometricFrobenius Y₀).hom r) M
  realizedPointComparison D l Ω (commonStagePullbackObject l Ω z P) L h ≪≫
    (stageRealization l Ω L).mapIso
      ((pointRationalFibre D l Fact.out
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).mapIso
          (commonStagePullbackComparison l Ω z P L h)) ≪≫
    (stageRealization l Ω L).mapIso
      ((rationalFibre D Y₀ l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) z).mapIso
          (commonStagePullbackComparison l Ω
            (localPositivePower (D.geometricFrobenius Y₀).hom r) M L h))

/-- The canonical compact-sections comparison to any enlarged coefficient stage.
This is the existing normalized whole-system operation mate, point scalar
comparison and balanced tensor tower at the identity compactification.
Source: Deligne (1.1.14), common-stage coefficient extension
(blueprint: lem-a1-proper-sections-semilinear-germs). -/
abbrev realizedSourceComparison
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : M.stage ≤ L) :=
  frobeniusCohomologyRealizedComparison D l Fact.out Y₀ Ω
    (Compactification.ofIsProper Y₀.hom) true M L h

end ProperSemilinearGerms

/-- Proper compact sections commute with the specified semilinear transport and
geometric germs, for rational coefficients, naturally in the complex M.
The index r means the positive exponent r+1, so every exponent at least one occurs.
The k-point is a map z with a_Y z=id; no Weil structure or finite-Tor condition occurs.
Source: Deligne, Weil II (1.1.7), (1.1.10)--(1.1.14), pp. 150--153;
Stacks 07A7 and 0D6D (blueprint: lem-a1-proper-sections-semilinear-germs).
Proof:
1. The identity compactification comparison of lem-pod-proper-coincidence-frobenius
identifies compact and ordinary transports, without identifying P_1 M with M.
2. Write A=La_Y*, R=R(a_Y)_*, P=Lg*, Q=Lh*, and Z_x=Lx*. The germ is Z_x of the
ordinary counit after the inverse comparison Z_x A≅id. Apply the unit-square-counit
identity mateEquiv_counit (lem-amb-mate-unit-counit) to the actual exchange mate:
A(E_M) followed by epsilon_(PM) equals theta_(RM)^(-1) followed by P(epsilon_M).
The equality holds on whole strict coefficient systems by
lem-coef-semilinear-derived-sections, and is carried through the total derived
inverse limit by prop-weil-pbc-rlim-functoriality and lem-fix-operation-reduction.
3. Pull this equality back by x. Associativity of the specified pullback comparisons
(lem-pod-integral-pullback-composition), using a_Y x=a_Y T(x)=id and
x g=h T(x) in composition order, identifies the two sides as
v_x^(PM) E_M = b_(1,x,M) Q(v_(T(x))^M), before point evaluation.
4. Apply Fib_s and precompose with iota_(RM). Naturality on every derived arrow
of the actual point transport (lem-weil-frobenius-point-transport-natural) gives
e_x^(PM) tau_M = Fib_s(b_(1,x,M)) iota_(Z_(T(x))M) e_(T(x))^M.
5. Induct on r+1 before contracting powers. At each step apply the one-step
identity at T^j(x); naturality of iota moves the preceding comparison across it.
Reassociate pullback comparisons with lem-pod-integral-pullback-composition.
The final inverse compositor on both iterated transports gives exactly rationalLeft
and rationalRight. Naturality of the counit, point transport, and compositors at
each step proves the displayed naturality for every integral arrow.
6. Apply raw scalar localization (def-weil-rationalization-karoubi), preserving
units, counits and comparisons by lem-fix-operation-reduction. On a pure tensor
arrow naturality is the scalar multiple of integral naturality; additivity gives
it for all rational arrows. Zero objects and the empty scheme require no exception. -/
theorem properSectionsSemilinearGermsRational
    (D : FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of D.k₀))) [IsProper Y₀.hom]
    (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (r : ℕ) (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) :
    (∀ M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left,
      ProperSemilinearGerms.rationalLeft D Y₀ l E z hz r M =
        ProperSemilinearGerms.rationalRight D Y₀ l E z hz r M) ∧
    (∀ (M N : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) (f : M ⟶ N),
      (ProperSemilinearGerms.rationalSections D Y₀ l E).map f ≫
          ProperSemilinearGerms.rationalLeft D Y₀ l E z hz r N =
        ProperSemilinearGerms.rationalLeft D Y₀ l E z hz r M ≫
          (ProperSemilinearGerms.rationalFibre D Y₀ l E z).map
            ((rationalDerivedPullback l E
              (localPositivePower (D.geometricFrobenius Y₀).hom r)).map f)) := by
  sorry

/-- The same derived germ identity with algebraically closed coefficients.
The equation is written in the faithful derived realization of bounded
finite-dimensional point complexes, retaining independent scheme and closure
universes. Naturality is tested at each common finite stage, and the final
conjunct explicitly requires compatibility with every further coefficient extension.
It conjugates the actual qbarLeft arrow by the canonical source and target
comparisons and equates it to the rational arrow at M.toStage h. Thus stages
and representatives are related by a stated equality, including identity extensions.
Source: Deligne, Weil II (1.1.7), (1.1.10)--(1.1.14), pp. 150--153;
Stacks 07A7 and 0D6D (blueprint: lem-a1-proper-sections-semilinear-germs).
Proof: use the six steps of properSectionsSemilinearGermsRational at M's coefficient
stage. Apply the exact coefficient-extension functor defining stageRealization;
every factor is the prescribed common-stage factor, by the definitions of point
fibre, pullback, cohomology transport, and the scalar comparisons of
lem-fix-operation-reduction. For a morphism choose one common finite extension
containing its two object stages and a representative; apply the rational naturality
formula there. The point scalar-extension comparisons of
lem-weil-frobenius-point-transport-natural identify all point transport factors.
For the final conjunct, scalar compatibility of the whole-system counit,
exchange mate and point transports identifies every factor under the normalized
source and target comparisons. Their balanced tensor towers and the normalized
pullback scalar comparisons give the displayed conjugation equality for every
L ≥ M.stage, including L=M.stage. This identifies further representatives and
proves independence of the representative. This gives naturality for every common-stage
arrow, including identities and objects represented at different finite fields. -/
theorem properSectionsSemilinearGerms
    (D : FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of D.k₀))) [IsProper Y₀.hom]
    (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (r : ℕ) (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) :
    (∀ M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left,
      ProperSemilinearGerms.qbarLeft D Y₀ l Ω z hz r M =
        ProperSemilinearGerms.qbarRight D Y₀ l Ω z hz r M) ∧
    (∀ (F : AlgebraicallyClosedCoefficients.Index l Ω)
      (M N : sfRationalConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) (D.geometricFiber Y₀).left)
      (f : M ⟶ N),
      (ProperSemilinearGerms.stageRealization l Ω F).map
          ((ProperSemilinearGerms.rationalSections D Y₀ l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).map f) ≫
          (ProperSemilinearGerms.stageRealization l Ω F).map
            (ProperSemilinearGerms.rationalLeft D Y₀ l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) z hz r N) =
        (ProperSemilinearGerms.stageRealization l Ω F).map
            (ProperSemilinearGerms.rationalLeft D Y₀ l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) z hz r M) ≫
          (ProperSemilinearGerms.stageRealization l Ω F).map
            ((ProperSemilinearGerms.rationalFibre D Y₀ l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) z).map
                ((rationalDerivedPullback l
                  (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
                  (localPositivePower (D.geometricFrobenius Y₀).hom r)).map f))) ∧
    (∀ (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
      (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : M.stage ≤ L),
      (ProperSemilinearGerms.realizedSourceComparison D Y₀ l Ω M L h).inv ≫
          ProperSemilinearGerms.qbarLeft D Y₀ l Ω z hz r M ≫
          (ProperSemilinearGerms.realizedTargetComparison D Y₀ l Ω z r M L h).hom =
        (ProperSemilinearGerms.stageRealization l Ω L).map
          (ProperSemilinearGerms.rationalLeft D Y₀ l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) z hz r (M.toStage h))) := by
  sorry

end WeilConjectures
