/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.LocalizingClosureExistence
public import Sheaf.Paper.IntegralDerivedCoefficientData
import Sheaf.Paper.DerivedNakayamaResolution
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
import Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts
import Sheaf.CategoryTheory.PretriangulatedKernelSplit
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.CategoryTheory.Monoidal.Mod
import Sheaf.SixFunctors.IntegralTensorInverseImage
import Sheaf.Paper.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-!
# Integral extension by zero

Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-int-compactness-ii,
`sk-cor-int-compactness-ii-extension-zero.md`, clauses (1)--(3); Stacks Project, Tag 09BP
(blueprint: det-cor-int-compactness-ii-extension-zero).

The coefficients are the continuous condensed integer ring of a finite extension of Q_l.
Reduction is actual derived tensor with its finite uniformizer-power quotient, regarded
as an integral module. Constructibility uses the recorded finite constant scalar models.
-/

@[expose] public section

set_option autoImplicit false

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Extension by zero along a quasi-compact open immersion is exact, preserves sums and
all existing small limits, commutes with uniformizer-power reduction, and preserves both
bounded constructibility and its localizing closure.

Source: blueprint main-20261015, sk-cor-int-compactness-ii-extension-zero, clauses (1)--(3);
Stacks Project, Tag 09BP (blueprint: det-cor-int-compactness-ii-extension-zero).

Proof plan:
1. The standing finite-type separated setting is qcqs (lem-weil-pbc-qcqs-over-affine).
Take the reduced closed complement (lem-weil-pbc-reduced-induced-closed-subscheme).
Apply lem-weil-pbc-proetale-ringed-open-closed. Cartesian coefficients identify its open
coefficient ring with the pulled-back integral ring (sk-prop-sfb-cartesian-coefficients).
The internal-module equivalence and sheaf tensor identify the module categories
(def-weil-pbc-internal-abelian-sheaf-module-equivalence, lem-weil-pbc-sheaf-tensor-closed,
sk-def-sfb-module-objects). Uniqueness of left adjoints identifies its exact extension
with sk-def-sfb-module-lower-shriek. Exact functor derived factorization supplies its
termwise triangulated derived functor (lem-weil-pbc-exact-functor-derived-factorization).
2. The sheaf adjunction preserves sums (lem-weil-pbc-left-adjoint-preserves-colimits),
and derived sums are termwise (det-def-localizing-closure-existence). Products and
sequential derived limits are preserved by det-sf-open-closed-extension-zero-limits.
Products exist by det-pe-products-derived (and, for sheaves, by
lem-weil-pbc-module-sheaves-limits-sectionwise). Express an existing small limit as the
kernel of the difference of its two product maps. This kernel is preserved by
lem-cor-int-compactness-ii-pretriangulated-kernel-split; additivity preserves the
difference. The product/equalizer construction then gives limit preservation
(lem-cor-int-compactness-ii-products-kernels-preserve-limits).
3. At n=0 the quotient ring and reductions are zero. For n positive,
det-pe-derived-nakayama-resolution identifies reduction with the natural cone of
multiplication by pi_E^n. The integral-linear termwise functor preserves the cone,
its differential, and its maps. This gives the natural reduction isomorphism.
The transition resolutions have pi_E in degree -1 and identity in degree zero;
the same termwise comparison respects those transitions.
4. Apply the integral extension-by-zero clause of sk-lem-int-tensor to preserve Dbc.
5. The full replete class of K whose extension lies in Loc(Dbc(X)) is triangulated
by step 1 and closed under sums by step 2. Step 4 says it contains Dbc(U).
Minimality in det-def-localizing-closure-existence gives the localizing assertion. -/
theorem integralExtensionByZero
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of k))] :
    (openImmersionLowerShriek (integralCoefficientRing l E) j).PreservesHomology ∧
    Functor.IsTriangulated
      (openImmersionLowerShriek (integralCoefficientRing l E) j).mapDerivedCategory ∧
    (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      (openImmersionLowerShriek (integralCoefficientRing l E) j).mapDerivedCategory) ∧
    PreservesLimitsOfSize.{u + 1, u + 1}
      (openImmersionLowerShriek (integralCoefficientRing l E) j).mapDerivedCategory ∧
    (∀ n : ℕ, Nonempty
      ((openImmersionLowerShriek (integralCoefficientRing l E) j).mapDerivedCategory ⋙
          integralReductionFunctor l E X n ≅
        integralReductionFunctor l E U n ⋙
          (openImmersionLowerShriek (integralCoefficientRing l E) j).mapDerivedCategory)) ∧
    (∀ K : integralDerived l E U,
      constantModelBoundedConstructible (integralCoefficientRing l E) U K →
      constantModelBoundedConstructible (integralCoefficientRing l E) X
        ((openImmersionLowerShriek (integralCoefficientRing l E) j).mapDerivedCategory.obj K)) ∧
    (∀ K : integralDerived l E U,
      localizingClosure (constantModelBoundedConstructible (integralCoefficientRing l E) U) K →
      localizingClosure (constantModelBoundedConstructible (integralCoefficientRing l E) X)
        ((openImmersionLowerShriek (integralCoefficientRing l E) j).mapDerivedCategory.obj
          K)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
