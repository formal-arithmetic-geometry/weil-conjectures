/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H6
-/
module

public import Sheaf.Paper.CompletedRlimFunctor
public import Sheaf.Paper.IntrinsicCompletion
public import Sheaf.Paper.CompletedTowerPullback
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.IntrinsicCompletionCompleted

/-!
# The normalized Koszul-to-quotient comparison over completed coefficients

Source: blueprint, proper base change, Koszul and quotient reconstruction, order 1248;
Stacks Tags 099L, 099M and 0A0E
(blueprint: lem-weil-pbc-completed-koszul-quotient-comparison).

This is the reconstruction comparison in the actual completed coefficient presentation,
with coefficient universe one above the scheme universe. The quotient unit is the
constant-tower adjunction unit followed by the specified strict quotient augmentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The localized explicit Koszul fiber is isomorphic to the derived strict quotient
limit, carrying its transported (u,0) unit to the actual quotient completion unit.
No completeness hypothesis on the input is required.

Source: blueprint `prop-weil-pbc-koszul-reconstruction`, comparison assertion;
Stacks Tags 099L, 099M and 0A0E
(blueprint: lem-weil-pbc-completed-koszul-quotient-comparison).

Proof: identify the finite constant quotient sheaves with the finite continuous-function
coefficient sheaves by their constants maps. Naturality for every quotient transition
identifies the completed rings and their projections. Restriction along this ring
isomorphism is an exact equivalence, preserving the tensor complexes, products and
specified Koszul unit. On a flat-term K-flat representative the Noetherian Koszul
augmentations to the positive quotient powers have pro-zero cones. Tensor by that model
and exact constant sheafification preserve the pro-zero assertion. The strict-tower
Roos triangle therefore makes the augmentation invertible after total derived inverse
limit. Cofinality of the powers of the generator ideal identifies the quotient limit.
Exact countable products on the pro-etale site identify the Koszul strict derived limit
with the published mapping fiber. Each augmentation sends the degree-zero element 1
to 1 and has zero homotopy component, so the isomorphism carries the published (u,0)
unit to the quotient unit. The latter is the constant-limit adjunction unit followed
by the strict quotient augmentation, by their common normalization on K-flat models.
Finally localization and the supplied realization transport the comparison to C and K.
This argument also covers an empty generator list, the zero ring and the empty scheme:
the same augmented towers and units are used, with the empty Koszul tensor the unit. -/
theorem completedKoszulQuotientComparison
    (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : d.derived T)
    (C : CochainComplex (reductionModules T (d.completedRing T)) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ K) :
    ∃ c : intrinsicCompletion T d r a ha K C eC ≅
        (completedRlim T (d.completedRing T)).obj ((completedReductionTower T d).obj K),
      intrinsicCompletionUnit T d r a ha K C eC ≫ c.hom =
        ((constLimAdj :
          (Functor.const ℕᵒᵖ : reductionModules T (d.completedRing T) ⥤ d.towers T) ⊣
            completedTowerLimit T (d.completedRing T)).mapDerivedCategoryRightDerivedAdjunction
              ).unit.app K ≫
          (completedRlim T (d.completedRing T)).map ((completedReductionTowerUnit d T).app K) := by
  sorry

end AlgebraicGeometry.Scheme
