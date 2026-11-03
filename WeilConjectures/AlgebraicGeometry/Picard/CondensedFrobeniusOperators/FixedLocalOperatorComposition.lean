/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.TraceFormulaCoefficientConventions.TraceFormulaFrobeniusOperators
public import WeilConjectures.AlgebraicGeometry.Picard.CondensedFrobeniusOperators.FixedPointTransportCoherence

/-! # Composition of fixed-point local operators

Source: latest blueprint, lem-trf-frobenius-degree-formula.proof.md, Step 1.
(blueprint: lem-trf-condensed-fixed-operator-composition)
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

/-- The local operator on a specified fixed geometric lift: the canonical fixed-point
transport followed by the iterated Weil map. This is a real composite, with no chosen data.
Source: latest blueprint, lem-trf-frobenius-degree-formula.proof.md, Step 1.
(blueprint: lem-trf-condensed-fixed-operator-composition). -/
def frobeniusFixedOperator (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left)
    (m : ℕ) (hm : 1 ≤ m) (hz : z ≫ F.coefficientFreeSchemeFrobeniusIterate Y₀ m = z) :
    End ((localFrobeniusFibre F Y₀ ell E n z).obj K.carrier.obj) :=
  (fixedPointStalkTransport F Y₀ ell E n hn z m hm hz).hom.app K.carrier.obj ≫
    (localFrobeniusFibre F Y₀ ell E n z).map (iteratedWeil F Y₀ ell E n hn K m).hom

include hEll in
/-- Fixed-lift local operators compose when their positive exponents add.

Source: literature/blueprint/latest/blueprint/sec-trace-formula/sk-c-proper-global/
lem-trf-frobenius-degree-formula.proof.md, Step 1, displayed recurrence.
(blueprint: lem-trf-condensed-fixed-operator-composition).

Proof: evaluate fixedPointStalkTransport_add on the strict Weil object K. Expand the
iterated Weil map by its compositor-aware cocycle, obtained by induction on the second
exponent of Iso.powStr. The base is the right unit law for derived pullback; the induction
uses pullback associativity and naturality of its compositor. Substitute this cocycle into
the operator at a+b. Under the fibre functor, the inverse compositor in the transport
cancels the forward compositor in the cocycle. Naturality of the transport at b, applied
to the Weil iterate at a, moves that iterate across the transport. Associativity now
identifies the result with the operator at a followed by the operator at b. Equality
coordinates cancel by equality induction and proof irrelevance. No perfection is needed.
-/
theorem frobeniusFixedOperator_add
    (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hza : z ≫ F.coefficientFreeSchemeFrobeniusIterate Y₀ a = z)
    (hzb : z ≫ F.coefficientFreeSchemeFrobeniusIterate Y₀ b = z)
    (hzab : z ≫ F.coefficientFreeSchemeFrobeniusIterate Y₀ (a + b) = z) :
    frobeniusFixedOperator F Y₀ ell E n hn K z (a + b) (by omega) hzab =
      frobeniusFixedOperator F Y₀ ell E n hn K z a ha hza ≫
        frobeniusFixedOperator F Y₀ ell E n hn K z b hb hzb := by
  sorry

end WeilConjectures.CondensedFrobeniusOperators
