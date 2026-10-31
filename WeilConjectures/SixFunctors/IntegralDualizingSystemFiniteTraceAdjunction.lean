/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingSystemTraceData
public import WeilConjectures.SixFunctors.CoefPairingExceptionalTests
import WeilConjectures.SixFunctors.IntegralDualizingSystemFiniteTraceEvaluation
import WeilConjectures.SixFunctors.IntegralDualizingSystemFiniteTraceAssembly

/-! # The normalized trace adjunction on finite sections tests

Source: prop-asd-internal-adjunction, exceptional counit Hom bijection;
prop-coef-integral-dualizing, proof paragraph 2.
(blueprint: lem-coef-system-finite-test-trace-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

include hl in
/-- Applying compact support and then the normalized trace is a Hom bijection
on the tensor of a pulled-back finite sections test with a reduced input.
This is the exceptional-counit step of the internal-adjunction chain; the
proper projection formula and both tensor-Hom transposes are separate steps.

Source: prop-asd-internal-adjunction, exceptional-adjunction step;
prop-coef-integral-dualizing, proof paragraph 2; Stacks 07A6, 08J9 and 0941.
(blueprint: lem-coef-system-finite-test-trace-adjunction).

Proof: resolve the test complex and the reduced input by flat-term K-flat
complexes, and the target by a simultaneous K-injective complex. The left
adjoint of tower evaluation at n is the free representable tower: maps from
it are exactly maps from the test complex to the nth evaluation. After the
sections left adjoint, pullback and tensor, the corresponding quotient-system
maps are consequently finite-level tensor maps, by scalar tensor-restriction
adjunction. This uses a cartesian reduced first input and permits arbitrary Q;
no normalized-transition hypothesis on Q is assumed. The same calculation
on the base gives finite-level maps from compact support of that tensor to
the evaluated base unit. Both calculations preserve postcomposition. Use
t.supportComparison and compactSupportSystemEvaluation to identify support,
and eQ n to identify the target with the specified finite dualizing object.
The equation t.trace_evaluation identifies the induced map between these two
Hom sets with postcomposition by integralDualizingFiniteSystemCounit, followed
by the inverse of t.unitEvaluation. Finite constructible origin for the
reduced input, its finite Tor interval from hK, and finite duality site
comparison transport this map to the ordinary etale exceptional-counit Hom
bijection. The ordinary etale adjunction allows the arbitrary pulled-back
scalar test complex. Transport back along the scalar and site equivalences.
All comparison arrows are units, counits, or the supplied natural support
isomorphism, so this proves bijectivity for the displayed map itself. This
step neither uses invertibility of a proper projection mate nor asserts
invertibility of the system exceptional transpose. -/
theorem integralDualizingSystem_finite_test_trace_bijective
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (Q : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n)
    (t : IntegralDualizingSystemTraceData D l E X S G Q eQ)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : finiteTorConstructibleIntegral l E X K) (n : ℕ)
    (T : DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))) :
    Function.Bijective (fun g :
      S.systemClosed.tensor.obj
        ((G.frame.testPull S.systemClosed G.baseTensors.systemClosed).obj
          ((coefPairingEvaluationLeft l E n).obj T), S.reduction.obj K) ⟶ coefTraceInput l E X Q ↦
      G.properModules.rightDerivedFunctor.map (G.openModules.mapDerivedCategory.map g) ≫
        t.trace) := by
  apply integralDualizingSystem_finite_trace_assembly D l hl E X S G Q eQ t K hK n T
  exact integralDualizingSystem_finite_trace_evaluation_bijective D l hl E X S G Q eQ t K hK n T

end WeilConjectures
