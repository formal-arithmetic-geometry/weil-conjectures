/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.CompletedPullback
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Sheaf.Paper.SbcCompletedOperations
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.RefinementCoefficientRealization
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.CompletedPullbackReduction
import Sheaf.Paper.PerfectProjectionFormula
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.Paper.CompletedAdicLevelwiseIsomorphismCones
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
import Sheaf.AlgebraicGeometry.FiniteProetaleSmoothBaseChange
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.Paper.NormalizedEtaleOriginWitnesses

/-! # Adic smooth base change

Source: blueprint, sec-smooth-base-change/sk-rem-rest, order 1443;
Stacks Tags 0EYU, 099N, 099M and 09AL
(blueprint: sbc-thm-adic-smooth-base-change).

The exchange is the published completed adjunction mate. The conditional clause
retains all four finite outputs and a single interval for every level.

## Main definitions and statements

- `sbcAdicFiniteCohomology`: the canonical finite coefficient presentation of cohomology.
- `adicSmoothBaseChange`: invertibility and conditional constructible landing.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Cohomology of a finite output, restricted along the canonical constant-to-function
coefficient isomorphism. This changes the coefficient presentation only and introduces
no constructibility or etale-origin condition.
Source: blueprint order 1443, finite-output clause; Stacks 09AJ
(blueprint: sbc-thm-adic-smooth-base-change). -/
def sbcAdicFiniteCohomology (W : Scheme.{u}) (n : ℕ)
    (J : DerivedCategory (pbcModules W ((pbcAdicRings W (pbcIntegralDatum l E)).obj
      (op n)))) (i : ℤ) :
    pbcModules W (adicLisseConstantRing W (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) :=
  (pbcRestrict (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom).obj
    ((DerivedCategory.homologyFunctor _ i).obj J)

/-- Smooth base change for the actual completed adjunction-mate exchange, and
constructible landing under one uniform interval for the four finite systems.
Source: blueprint order 1443, sec-smooth-base-change/sk-rem-rest;
Stacks Tags 0EYU, 099N, 099M and 09AL
(blueprint: sbc-thm-adic-smooth-base-change).

Proof:
1. Membership gives intrinsic completeness. Reindex the positive quotient tower by
   n+1. Choose each assumed bounded constructible etale origin solely for applying
   the finite theorem; the integral exchange remains the specified canonical map.
2. Apply sbc-thm-finite-proetale-smooth-base-change at each finite quotient. Smoothness,
   qcqs, noetherianity and invertibility of its order give invertible finite exchange.
   Further uniformizer quotients are earlier levels, by canonical normalization.
3. Use prop-weil-pbc-direct-image-limits for completeness of both direct images and
   lemma-weil-pbc-completed-pullback-reduction for the two completed pullbacks.
   Apply lemma-weil-pbc-perfect-projection-formula to the perfect quotient on g and h.
   The canonical coefficient squares and ring-sheaf change adjunction identify these
   reductions with the four displayed finite operations after scalar restriction.
4. lem-sbc-completed-operations-linear-natural-exchange identifies the reduction of
   this very mate with finite exchange under those comparisons. Scalar restriction
   reflects isomorphisms, so each actual quotient reduction of the mate is invertible.
5. lem-weil-pbc-levelwise-isomorphism-cones detects invertibility between the two
   complete endpoints from these reductions. Both endpoints are over X.
6. Under the interval hypothesis their actual reductions have constructible cohomology
   in that same interval. The constant-completion quotient identification makes the
   cohomology comparisons quotient-linear: locally lift a quotient scalar to A_X,
   apply A_X-linearity, and use that the ideal power kills both cohomology sheaves.
   Normalized constructible local effectivity supplies the common stratified local
   bounded adic-lisse models for each endpoint's canonical tower.
7. Finite-ring constructible derived origin supplies bounded constructible etale
   origins of those endpoint reductions. K-flat tensor pullback and exact comparison
   inverse image identify successive reductions. Exactness and the sheaf unit reflect
   vanishing, so the etale tensors remain bounded below. Bounded-below comparison is
   fully faithful: uniquely lift the quotient normalization and its inverse. Applying
   comparison inverse image to the two composites gives the normalization cocycle;
   cancel the origin isomorphism and use faithfulness to get the witness cocycle and
   identity normalization.
8. Completeness, uniform local models and compatible origins give both membership
   witnesses in the integral constructible category. Fullness puts the same mate and
   its inverse in that category, giving the final IsIso assertion.
-/
theorem adicSmoothBaseChange
    {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (sq : ChosenCartesianSquare h e f g)
    [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
    [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (_hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (_hl : IsUnit (l : Γ(S, ⊤)))
    (_horder : ∀ n : ℕ,
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(S, ⊤)) ∧
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(X, ⊤)) ∧
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(T, ⊤)) ∧
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(Y, ⊤)))
    (K : PbcIntegralConstructible l E T)
    (_horigin : ∀ n : ℕ,
      ∃ L : Etale.BoundedConstructibleDerivedCategory
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) T,
        Nonempty ((pbcDerivedFunctionRealization T (pbcIntegralDatum l E) n).obj
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1}
              (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) T).mapDerivedCategory.obj L.obj) ≅
          (sbcReduction l E T n).obj K.obj)) :
    IsIso (sbcExchangeApp l E sq ((pbcConstructibleInclusion l E T).obj K)) ∧
    ((∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞)) →
      (∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ, ∀ i : ℤ,
        (IsConstructibleProEtaleCoefficientModuleSheaf S
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E S n
          ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj K.obj)) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E S n
          ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj K.obj)) i))) ∧
        (IsConstructibleProEtaleCoefficientModuleSheaf X
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePull l E f n).obj
            ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj K.obj))) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePull l E f n).obj
            ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj K.obj))) i))) ∧
        (IsConstructibleProEtaleCoefficientModuleSheaf Y
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E Y n
          ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj K.obj)) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E Y n
          ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj K.obj)) i))) ∧
        (IsConstructibleProEtaleCoefficientModuleSheaf X
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePush l E h n).obj
            ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj K.obj))) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePush l E h n).obj
            ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj K.obj))) i)))) →
      ∃ (hB : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
          ((sbcPull l E f).obj ((sbcPush l E g).obj
            ((pbcConstructibleInclusion l E T).obj K))).obj)
        (hD : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
          ((sbcPush l E h).obj ((sbcPull l E e).obj
            ((pbcConstructibleInclusion l E T).obj K))).obj),
        IsIso (ObjectProperty.homMk
          (P := PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E))
          (X := ⟨((sbcPull l E f).obj ((sbcPush l E g).obj
            ((pbcConstructibleInclusion l E T).obj K))).obj, hB⟩)
          (Y := ⟨((sbcPush l E h).obj ((sbcPull l E e).obj
            ((pbcConstructibleInclusion l E T).obj K))).obj, hD⟩)
          (sbcExchangeApp l E sq ((pbcConstructibleInclusion l E T).obj K)).hom)) := by
  sorry

end WeilConjectures
