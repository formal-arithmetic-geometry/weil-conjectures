/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.FiniteFieldFiber
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Paper.ProEtaleResidueTorTest
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Residue reduction controls integral Tor amplitude

Source: Weil conjectures blueprint, `sec-six-functors/sk-prop-sf-biduality-general`,
`lem-coef-integral-residue-tor`, order 2133 (blueprint: lem-coef-integral-residue-tor).

The finite reduction API uses index `n` for exponent `n+1`. In particular index `0`
is the residue reduction. Equality of the object predicates states equality of the
corresponding full subcategories of the same completed integral derived category.
-/

@[expose] public section

set_option autoImplicit false

universe d u

open CategoryTheory AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Bounds on residue cohomology give the same Tor interval at every finite level,
and the integral constructible and integral finite-Tor full subcategories coincide.
This does not identify constructibility with site-perfectness.

Source: blueprint order 2133 (blueprint: lem-coef-integral-residue-tor).
Proof:
1. Choose a K-flat resolution P of a representative of K, using
lem-pc-kflat-resolution. The reduction at exponent n+1 is represented by
Q_n = P tensor A_{n+1}, by def-weil-integral-derived-reduction. Its bounded
constructibility is part of def-weil-derived-complete-integral-detailed.
2. For every acyclic A_{n+1}-complex N, restriction to the completed coefficient
ring is acyclic. The balanced identification (P tensor A_{n+1}) tensor N = P tensor N
makes Q_n K-flat, by def-pc-kflat-complex and def-pur-sheaf-tensor-product.
The forward map sends (x tensor c) tensor z to x tensor cz; the inverse sends
x tensor z to (x tensor 1) tensor z. These maps respect restrictions and differentials.
Thus lem-pur-derived-change-of-rings computes the residue tensor of Q_n as
P tensor kappa, representing K_1. The composite coefficient projection is the
level-one projection, componentwise in the defining inverse limit.
3. Apply lem-sf-proetale-residue-tor-test to every bounded constructible reduction.
Its residue tensor has the assumed cohomology bounds, so its Tor amplitude is [a,b].
4. The common cohomology interval in def-weil-derived-complete-integral-detailed
bounds the residue reduction. Step 3 supplies one Tor interval for every reduction,
which is exactly def-weil-finite-tor-amplitude. Conversely its integral predicate
includes bounded constructible derived-complete membership. Extensionality gives
equality of the object predicates and hence of their full subcategories. -/
theorem integral_residue_tor
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : AlgebraicGeometry.Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] :
    (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X)),
      sfIntegralConstructible l E X K →
      ∀ a b : ℤ, a ≤ b →
        (∀ i : ℤ,
          i ∈ proEtaleCohomologicalSupport
            ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K) → a ≤ i ∧ i ≤ b) →
        ∀ n : ℕ,
          HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
            ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) a b) ∧
      sfIntegralConstructible l E X =
        finiteTorConstructibleIntegral l E X := by
  sorry

end WeilConjectures
