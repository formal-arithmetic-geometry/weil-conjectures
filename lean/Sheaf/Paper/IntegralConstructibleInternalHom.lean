/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.IntegralHomReductionComparison
public import Sheaf.Paper.DerivedCompleteIntegralDetailed
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
import Sheaf.Algebra.Homology.DerivedTensor
import Sheaf.Paper.IntegralResidueTor
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import Sheaf.Paper.FiniteConstructibleHom
import Sheaf.Paper.IntegralHomReduction
import Sheaf.Paper.SfIntegralConstructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-! # Constructible integral internal Hom

Source: Weil conjectures blueprint, `sec-six-functors/sk-prop-sf-biduality-general`,
`cor-coef-integral-internal-hom`, order 2147
(blueprint: cor-coef-integral-internal-hom).
The index `n : ℕ` denotes the positive exponent `n + 1` throughout.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace WeilConjectures

/-- The ambient completed-coefficient Hom is constructible and derived complete;
its canonical evaluation-defined reductions are isomorphisms, with the stated uniform
Tor interval over the finite quotient coefficient sheaf.

Source: blueprint order 2147 (blueprint: cor-coef-integral-internal-hom).
Proof:
1. The defining integral predicate makes K and L complete and their residue reductions
bounded constructible. Choose intervals bounding residue cohomology (any interval works
for zero). Apply lem-coef-integral-residue-tor separately to obtain uniform finite-level
Tor intervals. The coefficient ring is the specified DVR, and l is invertible on X
because X is over the algebraic closure of a field of characteristic p different from l.
2. Apply lem-coef-integral-hom-reduction to the ambient internal Hom H. Completeness of
L implies completeness of H. The reduction comparison, defined as the transpose of
reduced evaluation, is an A_n-linear isomorphism, without site-perfectness of K.
3. By lem-kun-dimension-finite-type choose one nonnegative bound d₀ for dim X, independent
of n. The empty scheme has dimension bottom and admits d₀ = 0.
4. Apply cor-weil-finite-constructible-hom on the pro-etale site at each positive level.
The reductions are bounded constructible and finite-Tor. It gives constructibility of
their internal Hom and Tor interval [c-b-2d,e-a+2d] for any supplied input intervals
and dimension bound. Transport through the canonical isomorphism from step 2.
5. Test the output Tor condition against the coefficient sheaf in degree zero.
The maps P tensor A_n → P, x tensor r ↦ rx, and x ↦ x tensor 1 give the unit isomorphism
on a K-flat representative. Hence output cohomology lies in the same uniform interval.
Together with steps 2 and 4 this is exactly def-weil-derived-complete-integral-detailed.
-/
theorem integral_constructible_internalHom
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    (K L : completedIntegralDerivedCategory l E X D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E X K)
    (hL : boundedConstructibleDerivedCompleteIntegral D l hl E X L) :
    boundedConstructibleDerivedCompleteIntegral D l hl E X
        ((homReductionHom (completedIntegralCommRingSheaf l E X D hl)).obj (op K, L)) ∧
      (∀ n : ℕ, IsIso (integralHomReductionComparison D l hl E X n K L)) ∧
      ∀ a b c e : ℤ, a ≤ b → c ≤ e →
        ∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) →
          (∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
            ((integralDerivedReduction l E X D hl n).obj K) a b) →
          (∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
            ((integralDerivedReduction l E X D hl n).obj L) c e) →
          ∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
            ((integralDerivedReduction l E X D hl n).obj
              ((homReductionHom (completedIntegralCommRingSheaf l E X D hl)).obj (op K, L)))
            (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ)) := by
  sorry

end WeilConjectures
