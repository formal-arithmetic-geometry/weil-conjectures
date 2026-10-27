/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.Paper.FrobeniusGeometricExchange
public import Sheaf.Paper.ProperCompactCoincidence
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfDerivedDirectImage
import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Paper.IdentityCompactificationSystemMate
import Sheaf.Paper.IntegralPullbackSystemComparison
import Sheaf.Paper.CompletedPrimitiveCounitComparison
import Sheaf.Paper.SfIntegralDirectImageConstructible
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.Paper.CompletedRlimFunctor

/-! # Identity-compactification normalization of the total-limit comparisons

Source: blueprint `prop-cohomological-finiteness`, proper case, current Step 3;
expanded DAG Step 6; Deligne, Weil I (1.3), p. 274
(blueprint: lem-pod-identity-compactification-limit-comparisons).

The maps below are the actual operation comparisons. Identity-open cancellation
is performed on whole strict systems, before scalar restriction and total limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor

namespace WeilConjectures.IdentityCompactificationLimit
open FrobeniusExchange

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The identity-open isomorphism fixed by the sheafification adjunction, not by
an arbitrary isomorphism of its endpoints.
Source: def-weil-extension-by-zero; blueprint proper-case Step 6
(blueprint: lem-pod-identity-compactification-limit-comparisons). -/
def openIso (Y : Scheme.{u}) : systemDerivedOpen l E (𝟙 Y) ≅ 𝟭 _ :=
  ((systemDerivedOpenAdjunction l E (𝟙 Y)).ofNatIsoRight
    (integralComparisonSystemUnit l E Y)).leftAdjointUniq Adjunction.id

variable (D : FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of D.k₀))) [IsProper Y₀.hom]

/-- The identity compactification of the proper geometric structure map.
Source: blueprint proper-case Step 6; Stacks 01W6
(blueprint: lem-pod-identity-compactification-limit-comparisons). -/
def compactification : Compactification (D.geometricFiber Y₀).hom :=
  @Compactification.ofIsProper _ _ (D.geometricFiber Y₀).hom
    (inferInstanceAs (IsProper (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))))

/-- The canonical whole-system map v = F_a(u), retaining every quotient transition.
Source: blueprint proper-case Step 6
(blueprint: lem-pod-identity-compactification-limit-comparisons). -/
def systemIso :
    systemDerivedOpen l E (𝟙 (D.geometricFiber Y₀).left) ⋙
        systemDirect l E (D.geometricFiber Y₀).hom ≅
      systemDirect l E (D.geometricFiber Y₀).hom :=
  isoWhiskerRight (openIso l E (D.geometricFiber Y₀).left) _ ≪≫ Functor.leftUnitor _

/-- The structure map is a morphism over its geometric base, using the existing
OverClass structure-map instance.
Source: blueprint geometric-fiber convention
(blueprint: lem-pod-identity-compactification-limit-comparisons). -/
instance structureIsOver :
    (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) :=
  inferInstanceAs (HomIsOver ((D.geometricFiber Y₀).left ↘ Spec (.of D.k))
    (Spec (.of D.k)))

/-- Properness of the actual geometric structure map is the existing base-change instance.
Source: Stacks 01W6; blueprint proper-case Step 6
(blueprint: lem-pod-identity-compactification-limit-comparisons). -/
instance structureProper : IsProper (D.geometricFiber Y₀).hom :=
  inferInstanceAs (IsProper (pullback.snd Y₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- The actual proper comparison: the projection-normalized compact realization,
then the total limit of F_a(u). The ordinary endpoint is the published simultaneous
integral direct-image model, whose Roos presentation is directImage_roos.
Source: blueprint proper-case Step 6, prop-weil-proper-compact-coincidence
(blueprint: lem-pod-identity-compactification-limit-comparisons). -/
def properComparison (hl : l ≠ D.p)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  letI : ∀ y : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField y) :=
    fun y ↦ (Eq.mp (congrArg IsUnit (map_natCast
      ((Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫
        (Spec (.of D.k)).Γevaluation y).hom l))
      ((finiteFieldDatumPrimeUnit D l hl).map
        ((Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫
          (Spec (.of D.k)).Γevaluation y).hom)).invertible
  letI := sfWeilPrimeInvertible D l hl Y₀
  (compactRealization l E D.k (finiteFieldDatumPrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (compactification D Y₀)).app M ≪≫
      (coefficientSequenceLimit l E (Spec (.of D.k))).mapIso
        ((systemIso l E D Y₀).app
          ((reduction l E (D.geometricFiber Y₀).left).obj M.obj))

/-- The left side L_s(h_S) alpha_!, in Lean's left-to-right composition convention.
Source: blueprint proper-case Step 6, source-comparison square
(blueprint: lem-pod-identity-compactification-limit-comparisons). -/
def alphaLeft (hl : l ≠ D.p)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  letI : ∀ y : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField y) :=
    fun y ↦ (Eq.mp (congrArg IsUnit (map_natCast
      ((Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫
        (Spec (.of D.k)).Γevaluation y).hom l))
      ((finiteFieldDatumPrimeUnit D l hl).map
        ((Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫
          (Spec (.of D.k)).Γevaluation y).hom)).invertible
  letI := sfWeilPrimeInvertible D l hl Y₀
  (compactAlpha l E D.k (finiteFieldDatumPrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (compactification D Y₀)
    (Spec.map (CommRingCat.ofHom
      (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
        (Fintype.ofFinite D.k₀) _ _ _).toRingHom))).app M ≫
    (coefficientSequenceLimit l E (Spec (.of D.k))).map
      ((integralComparisonDerivedSequencePullback l E (Spec.map (CommRingCat.ofHom
        (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
          (Fintype.ofFinite D.k₀) _ _ _).toRingHom))).map
        ((systemIso l E D Y₀).hom.app
          ((reduction l E (D.geometricFiber Y₀).left).obj M.obj)))

/-- The right side alpha_* Lg_s^*(kappa_M), using exactly sourceComparison.
Source: blueprint proper-case Step 6, source-comparison square
(blueprint: lem-pod-identity-compactification-limit-comparisons). -/
def alphaRight (hl : l ≠ D.p)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  (integralDerivedPullback l E (Spec.map (CommRingCat.ofHom
    (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
      (Fintype.ofFinite D.k₀) _ _ _).toRingHom))).map
        (properComparison l E D Y₀ hl M).hom ≫
    (sourceComparison l E (systemDirect l E (D.geometricFiber Y₀).hom)
      (Spec.map (CommRingCat.ofHom
        (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
          (Fintype.ofFinite D.k₀) _ _ _).toRingHom))).app M.obj

/-- The left side kappa_{M'} beta_!, where M' is the specified derived pullback.
Source: blueprint proper-case Step 6, target-comparison square
(blueprint: lem-pod-identity-compactification-limit-comparisons). -/
def betaLeft (hl : l ≠ D.p)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  letI : ∀ y : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField y) :=
    fun y ↦ (Eq.mp (congrArg IsUnit (map_natCast
      ((Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫
        (Spec (.of D.k)).Γevaluation y).hom l))
      ((finiteFieldDatumPrimeUnit D l hl).map
        ((Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫
          (Spec (.of D.k)).Γevaluation y).hom)).invertible
  letI := sfWeilPrimeInvertible D l hl Y₀
  (compactBeta l E D.k (finiteFieldDatumPrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (compactification D Y₀)
    (D.geometricFrobenius Y₀).hom).app M ≫
      (properComparison l E D Y₀ hl
        ((constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom).obj M)).hom

/-- The right side beta_* L_s(h_T), with h_T = F_a(u_{G_Y R_Y M}).
Source: blueprint proper-case Step 6, target-comparison square
(blueprint: lem-pod-identity-compactification-limit-comparisons). -/
def betaRight (hl : l ≠ D.p)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  (coefficientSequenceLimit l E (Spec (.of D.k))).map
    ((systemIso l E D Y₀).hom.app
      ((integralComparisonDerivedSequencePullback l E (D.geometricFrobenius Y₀).hom).obj
        ((reduction l E (D.geometricFiber Y₀).left).obj M.obj))) ≫
    (whiskerRight (reductionPullbackIso l E (D.geometricFrobenius Y₀).hom).inv
      (systemDirect l E (D.geometricFiber Y₀).hom ⋙
        coefficientSequenceLimit l E (Spec (.of D.k)))).app M

/-- Scalar localization of the ambient integral category, using the existing constant
coefficient action. Its restriction to constructible objects is the recorded raw
rationalization, with unchanged integral representatives and tensor-with-one Hom maps.
Source: def-weil-rationalization-karoubi; blueprint coefficient passage
(blueprint: lem-pod-identity-compactification-limit-comparisons). -/
def localization :=
  ScalarLocalization.localization (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory (scalarReductionSource l E (Spec (.of D.k))))
    (Padic.coefficientExtensionUniformizer l E)

/-- The source-square left composite after scalar localization.
Source: def-weil-frobenius-square-exchange, rational coefficient passage
(blueprint: lem-pod-identity-compactification-limit-comparisons). -/
def rationalAlphaLeft (hl : l ≠ D.p)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  (localization l E D).map (alphaLeft l E D Y₀ hl M)

/-- The source-square right composite after scalar localization.
Source: def-weil-frobenius-square-exchange, rational coefficient passage
(blueprint: lem-pod-identity-compactification-limit-comparisons). -/
def rationalAlphaRight (hl : l ≠ D.p)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  (localization l E D).map (alphaRight l E D Y₀ hl M)

/-- The target-square left composite after scalar localization.
Source: def-weil-frobenius-square-exchange, rational coefficient passage
(blueprint: lem-pod-identity-compactification-limit-comparisons). -/
def rationalBetaLeft (hl : l ≠ D.p)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  (localization l E D).map (betaLeft l E D Y₀ hl M)

/-- The target-square right composite after scalar localization.
Source: def-weil-frobenius-square-exchange, rational coefficient passage
(blueprint: lem-pod-identity-compactification-limit-comparisons). -/
def rationalBetaRight (hl : l ≠ D.p)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  (localization l E D).map (betaRight l E D Y₀ hl M)

/-- Both specified total-limit comparison squares commute under the actual proper
comparison at the identity compactification. In particular this compares the maps,
not merely their finite evaluations or the isomorphism classes of their endpoints.
Source: blueprint prop-cohomological-finiteness, proper case, expanded Step 6
(blueprint: lem-pod-identity-compactification-limit-comparisons).
Proof: (1) Properness is stable under base change. Geometric Frobenius is a scheme
isomorphism; isomorphism-derived-pullback preserves integral constructibility.
(2) By identityCompactificationSystemMate and the proper integral tower comparison,
the whole-system identity-open isomorphism gives kappa_N = L_s(F_a(u_{R_Y N}))
for N=M,M', in the fixed projection-normalized compact realization.
(3) Unpack sourceComparison: it is the primitive pullback realization followed by
L_s G_s of the whole-system reduction/limit adjunction counit, as in
completedPrimitiveCounitComparison and coefficientDerivedSystemEvaluationCalculus.
(4) Naturality of that counit at F_a(u), then naturality of the primitive realization,
gives alphaLeft = alphaRight, before any finite evaluation is made.
(5) The pullback/reduction isomorphism of integralPullbackSystemComparison gives
beta_* = L_s F_a(d_M inverse). The compact beta uses J of the same inverse, with
the inverse projection-normalized compact realization.
(6) Naturality of u at d_M inverse gives betaLeft = betaRight after F_a and L_s;
completedRlim functoriality retains every quotient transition.
(7) Apply scalar localization to these equal morphisms for E; at a common finite
coefficient field apply the stage inclusion to obtain the Qbar_l representatives.
These are precisely the coefficient conventions of def-weil-frobenius-square-exchange;
only integral objects, never rational ones, were reduced modulo the uniformizer. -/
theorem identityCompactificationLimitComparisons (hl : l ≠ D.p)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :
    alphaLeft l E D Y₀ hl M = alphaRight l E D Y₀ hl M ∧
      betaLeft l E D Y₀ hl M = betaRight l E D Y₀ hl M ∧
      rationalAlphaLeft l E D Y₀ hl M = rationalAlphaRight l E D Y₀ hl M ∧
      rationalBetaLeft l E D Y₀ hl M = rationalBetaRight l E D Y₀ hl M ∧
      (∀ (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
        (E₀ : AlgebraicallyClosedCoefficients.Index l Ω)
        (N : sfIntegralConstructibleCategory l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀) (D.geometricFiber Y₀).left),
        rationalAlphaLeft l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀)
            D Y₀ hl N =
          rationalAlphaRight l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀)
            D Y₀ hl N ∧
        rationalBetaLeft l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀)
            D Y₀ hl N =
          rationalBetaRight l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀)
            D Y₀ hl N) := by
  sorry

end WeilConjectures.IdentityCompactificationLimit
