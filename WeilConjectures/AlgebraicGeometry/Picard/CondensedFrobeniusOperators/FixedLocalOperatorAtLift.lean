/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.CondensedFrobeniusOperators.FixedLocalOperatorComposition

/-! # Rational-point coordinates for a fixed-lift operator

Source: latest blueprint, lem-trf-frobenius-degree-formula.proof.md, Step 1.
(blueprint: lem-trf-condensed-fixed-operator-at-lift)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false


universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilConjectures.CondensedFrobeniusOperators
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

variable (F : FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of F.k₀)))
  [IsSeparated Y₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ F.p)
  (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
  (n : ℕ) (hn : 1 ≤ n) (K : FiniteStrictWeilComplex F Y₀ ell E n hn)

/-- The operator on a fixed lift is the owning rational-point local operator in
its explicitly equal point coordinates.

Source: literature/blueprint/latest/blueprint/sec-trace-formula/sk-c-proper-global/
lem-trf-frobenius-degree-formula.proof.md, Step 1, identifying the chosen lift operator.
(blueprint: lem-trf-condensed-fixed-operator-at-lift).

Proof: eliminate the equality of the rational-point lift and z. The fixedness proof is
then equal to rationalPoint_schemeFrobenius_fixed by proof irrelevance. Expand the three
factors of fixedPointStalkTransport: the inverse equality isomorphism, the pullback
compositor, and the scheme/Galois comparison, followed by point sections. Evaluation
commutes with whiskering and sends the associator component to the identity. These are
exactly the three factors of fixedPointReturn after applying point sections, because
finiteSchemeGaloisComparison is the component of finiteSchemeGaloisComparisonFunctor.
Both local operators append the same iterated Weil morphism. Functoriality of point
sections, and the identity coordinate isomorphism in localFrobeniusAtLift, give equality.
-/
theorem frobeniusFixedOperator_atLift
    (m : ℕ) (hm : 1 ≤ m) (y : F.extensionPoints Y₀ m hm)
    (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left)
    (hy : extensionPointGeometry F Y₀ m hm y = z)
    (hz : z ≫ F.coefficientFreeSchemeFrobeniusIterate Y₀ m = z) :
    frobeniusFixedOperator F Y₀ ell E n hn K z m hm hz =
      localFrobeniusAtLift F Y₀ ell E n hn hEll K m hm y z hy := by
  sorry

end WeilConjectures.CondensedFrobeniusOperators
