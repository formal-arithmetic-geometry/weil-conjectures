/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.AlgebraicGeometry.Noetherian

import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.Paper.CompletedOpenExchangeTransport
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.IntrinsicCompletionCompleted
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.OpenExtensionFiniteTor
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.Paper.SfDerivedComplete
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.WeilCompletedTensorReflector
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Paper.CompactificationCoherence
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Open compact supports preserve finite-Tor constructibility

Source: Weil blueprint, main-20261015, sec-six-functors/sk-lem-sf-open-ctf,
order 2499 (blueprint: sk-lem-sf-open-ctf).

## Main statements

- `sfOpenCompactSupport_finite`: finite-Tor constructibility and both finite intervals.
- `sfOpenCompactSupport_integral`: integral constructibility, actual cohomological
  bounds and the same Tor interval for every positive reduction.
- `sfOpenCompactSupport_rational` and `sfOpenCompactSupport_qbar`: the two standard
  classes at the field stages, where finite-Tor constructibility means constructibility.

The three value wrappers only supply the quasi-compactness instance already implied
by the finite-type hypotheses before calling the recorded compact-support definitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

section Values
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (k : Type u) [Field k] (hl : IsUnit (l : k))
  {U Y : Scheme.{u}}
  [U.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  (j : U ⟶ Y) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
  (c : Compactification j)

/-- The recorded integral compact-support value, with quasi-compactness of the open
immersion inferred from the finite-type target over a field. This is an elaboration
wrapper for `sfIntegralCompactSupportValue`, using the same compactification and
Roos-limit value, not a new choice or a new coefficient category.
Source: blueprint main-20261015, sk-lem-sf-open-ctf, proof steps 1 and 5
(blueprint: sk-lem-sf-open-ctf). -/
def sfOpenIntegralCompactSupportValue (K : sfIntegralConstructibleCategory l E U) :
    sfIntegralConstructibleCategory l E Y := by
  letI : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  exact sfIntegralCompactSupportValue l E k hl c K

/-- The recorded rational compact-support value, supplying only the geometric
quasi-compactness instance as in the integral wrapper. The input is any object of
the raw rationalized category; its `.obj` is its integral representative.
Source: blueprint main-20261015, sk-lem-sf-open-ctf, proof step 6
(blueprint: sk-lem-sf-open-ctf). -/
def sfOpenRationalCompactSupportValue (K : sfRationalConstructibleCategory l E U) :
    sfRationalConstructibleCategory l E Y := by
  letI : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  exact sfRationalCompactSupportValue l E k hl c K.obj

/-- The recorded common-stage compact-support value, keeping the input's coefficient
stage and applying the recorded rational value there. Only the quasi-compactness
instance is supplied; the pair and its rational object are exactly the recorded ones.
Source: blueprint main-20261015, sk-lem-sf-open-ctf, proof step 7
(blueprint: sk-lem-sf-open-ctf). -/
def sfOpenQbarCompactSupportValue
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω U) :
    generalAlgebraicallyClosedConstructibleCategory l Ω Y := by
  letI : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  exact sfQbarCompactSupportValue l k hl Ω c K.stage K.obj.obj
end Values

section Statements
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {U Y : Scheme.{u}}
  [hUOver : U.Over (Spec (.of D.k))] [hYOver : Y.Over (Spec (.of D.k))]
  [hUft : LocallyOfFiniteType (U ↘ Spec (.of D.k))]
  [hUqc : QuasiCompact (U ↘ Spec (.of D.k))]
  [hYft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [hYqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  (j : U ⟶ Y) [hjOpen : IsOpenImmersion j] [hjOver : j.IsOver (Spec (.of D.k))]
  (c : Compactification j) (a b : ℤ) (hab : a ≤ b)

include D hl hab hUOver hYOver hUft hUqc hYft hYqc hjOpen hjOver

/-- Finite-coefficient compact supports for an open immersion preserve finite-Tor
constructibility and the given cohomological and Tor interval `[a,b]`.
Source: blueprint main-20261015, sk-lem-sf-open-ctf, order 2499
(blueprint: sk-lem-sf-open-ctf).

Proof: finite type over the field makes U and Y Noetherian, hence j quasi-compact
(lem-weil-pbc-finite-type-over-noetherian). Localize the pro-etale site at U
(lem-weil-proetale-weakly-etale-localization). Exactness of extension by zero
(lem-pur-site-restriction-module-adjunction-exact) gives H^r(j_!K) = j_!H^r(K)
(lem-weil-pbc-exact-functor-complex-cohomology), retaining the interval.
Extend each finite constructible partition on U by the reduced closed complement
(lem-weil-pbc-reduced-induced-closed-subscheme). The restrictions are the original
finite locally constant module on each old stratum and zero on the complement
(lem-weil-pbc-proetale-ringed-open-closed and the pullback-composition lemma).
The finite open tensor identity, tested against every degree-zero module sheaf,
retains the Tor interval (lem-trf-open-ctf). The trivial compactification computes
j_!; bounded constructible objects have etale origin
(lem-sf-proetale-constructible-origin), so compactification coherence identifies
this value with the specified c (prop-compactification-coherence-detailed). -/
theorem sfOpenCompactSupport_finite
    (n : ℕ) (hn : 1 ≤ n)
    (K : finiteTorConstructibleCategory l E n hn U)
    (hcoh : proEtaleCohomologicalSupport K.obj ⊆ Set.Icc a b)
    (hTor : HasProEtaleTorAmplitude U (Padic.coefficientExtensionRing l E n) K.obj a b) :
    finiteTorConstructible l E n hn Y
        ((@sfIntrinsicCompactSupport U Y j c (Padic.coefficientExtensionRing l E n) _
          (Padic.finite_coefficientExtensionRing l E n hn)).obj K.obj) ∧
      proEtaleCohomologicalSupport
        ((@sfIntrinsicCompactSupport U Y j c (Padic.coefficientExtensionRing l E n) _
          (Padic.finite_coefficientExtensionRing l E n hn)).obj K.obj) ⊆ Set.Icc a b ∧
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n)
        ((@sfIntrinsicCompactSupport U Y j c (Padic.coefficientExtensionRing l E n) _
          (Padic.finite_coefficientExtensionRing l E n hn)).obj K.obj) a b := by
  sorry

/-- Integral compact supports for an open immersion preserve finite-Tor constructibility,
the actual cohomological interval and the same uniform Tor interval at every reduction.
Source: blueprint main-20261015, sk-lem-sf-open-ctf, order 2499
(blueprint: sk-lem-sf-open-ctf).

Proof: the completed ring sheaf restricts to the completed ring on U since its
inverse-limit sections and finite projections agree. Exact extension by zero
therefore preserves actual integral cohomological vanishing, as in the finite clause.
The ringed-slice tensor identity (lem-weil-pbc-ringed-slice-extension-tensor),
degreewise on total tensor complexes, shows that extension by zero sends K-flat
resolutions to K-flat resolutions. Derived change of rings then identifies every
finite reduction of j_!K with j_! of the corresponding reduction of K, compatibly
with all quotient transitions. Apply the finite constructibility/Tor argument to
each reduction, retaining the uniform bound independent of the exponent.
For completeness use lem-cbc-completed-extension-zero-comparison on the identity
open square. Identify Koszul completeness and quotient-tower completeness, including
the units, via lem-weil-pbc-constant-completion-equivalence and the Koszul reflector.
The completed constant-sheaf reduction theorem identifies the adic coefficient model
with the actual completed coefficient sheaf, since the finite quotients are finite.
The DVR and finite-quotient lemmas verify the coefficient hypotheses without adding
an assumption. Thus the extended object is complete with uniformly bounded
constructible reductions, and has the same uniform Tor interval.
Finally the reduction-tower identifications identify it naturally with the recorded
integral compact-support value, as specified in def-weil-integral-rational-qbar-compact-support;
use the functorial completion unit, rather than unrelated choices of Roos triangles. -/
theorem sfOpenCompactSupport_integral
    (K : sfIntegralConstructibleCategory l E U)
    (hK : finiteTorConstructibleIntegral l E U K.obj)
    (hupper : sfIntegralStandardClass l E U true b K)
    (hlower : sfIntegralStandardClass l E U false a K)
    (hTor : ∀ n : ℕ, HasProEtaleTorAmplitude U
      (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension l E U n).obj K.obj) a b) :
    finiteTorConstructibleIntegral l E Y
        (sfOpenIntegralCompactSupportValue l E D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) j c K).obj ∧
      sfIntegralStandardClass l E Y true b
        (sfOpenIntegralCompactSupportValue l E D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) j c K) ∧
      sfIntegralStandardClass l E Y false a
        (sfOpenIntegralCompactSupportValue l E D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) j c K) ∧
      ∀ n : ℕ, HasProEtaleTorAmplitude Y
        (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension l E Y n).obj
          (sfOpenIntegralCompactSupportValue l E D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) j c K).obj) a b := by
  sorry

/-- Rational compact supports for an open immersion preserve the raw bounded
constructible category and every standard cohomological interval. No numerical
Tor condition is imposed at field coefficients.
Source: blueprint main-20261015, sk-lem-sf-open-ctf, order 2499
(blueprint: sk-lem-sf-open-ctf).

Proof: the preceding exact extension argument also preserves the integral bounded
constructible category without its Tor hypothesis. Extension by zero is linear on
integral module sheaves and roofs, so it acts on rational Hom tensors by
f tensor e mapped to j_!f tensor e (def-weil-rationalization-karoubi).
The natural integral comparison with the prescribed compact-support operation
rationalizes to identify this action with the prescribed rational operation.
For the upper bound choose an integral upper-bound witness and its rational
isomorphism from def-weil-constructible-standard-tstructure. Extend that witness
exactly and apply the rational operation to the isomorphism. Choose a separate
lower-bound witness and repeat; no integral representative satisfying both bounds
is assumed. This gives both standard classes in the original interval. -/
theorem sfOpenCompactSupport_rational
    (K : sfRationalConstructibleCategory l E U)
    (hupper : sfRationalStandardClass l E U true b K)
    (hlower : sfRationalStandardClass l E U false a K) :
    sfRationalStandardClass l E Y true b
        (sfOpenRationalCompactSupportValue l E D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) j c K) ∧
      sfRationalStandardClass l E Y false a
        (sfOpenRationalCompactSupportValue l E D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) j c K) := by
  sorry

/-- Common-stage compact supports preserve the bounded constructible category and
every standard cohomological interval, with no numerical Tor assertion at this stage.
Source: blueprint main-20261015, sk-lem-sf-open-ctf, order 2499
(blueprint: sk-lem-sf-open-ctf).

Proof: retain the representative coefficient field and apply the rational operation
(def-weil-algebraically-closed-coefficients). Coefficient comparisons
(lem-fix-operation-reduction) descend its morphisms to the common-stage category.
Represent an upper-bound witness and its witnessing isomorphism at a common finite
coefficient field and use the rational result there. Repeat independently for the
lower bound. The common-stage standard classes are isomorphism closures of precisely
these rational classes (def-weil-constructible-standard-tstructure), so both bounds
pass to the output. Dctf equals Dbc by definition at both field stages. -/
theorem sfOpenCompactSupport_qbar
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω U)
    (hupper : sfCommonStageStandardClass l U Ω true b K)
    (hlower : sfCommonStageStandardClass l U Ω false a K) :
    sfCommonStageStandardClass l Y Ω true b
        (sfOpenQbarCompactSupportValue l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) j c Ω K) ∧
      sfCommonStageStandardClass l Y Ω false a
        (sfOpenQbarCompactSupportValue l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) j c Ω K) := by
  sorry
end Statements
end WeilConjectures
