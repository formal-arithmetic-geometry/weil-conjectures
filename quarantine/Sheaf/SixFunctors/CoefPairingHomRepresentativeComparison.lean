/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q9
-/
module

public import Sheaf.SixFunctors.CoefTowerEvaluationPairingData
import Sheaf.SixFunctors.CoefHomTowerScalarModel

/-! # Representative and integral finite Hom comparison

Source: blueprint prop-coef-integral-dualizing, proof paragraph 2,
Hom-complex comparison (blueprint: lem-coef-pairing-hom-representative-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Compare the fixed derived Hom tower with every simultaneous K-injective model
and with its integral finite Hom descriptions. No compactification is involved.

Source: blueprint prop-coef-integral-dualizing, proof paragraph 2; Stacks 08J9,
0A8Z and 0941 (blueprint: lem-coef-pairing-hom-representative-comparison).

Proof: the normalized reduction adjunction identifies S.reduction with derived
extension from the constant completed-ring sequence. Apply coefHomTowerScalarModel
on that ringed sequence site, and the derived point-square comparison, to identify
coefPairingHom with global Hom from the constant input into restricted Q. Resolve
the restricted Q by the supplied simultaneous K-injective tower I. Hom into I
preserves quasi-isomorphisms in the first argument, so an arbitrary representative
P can be used: compare it through a flat-term K-flat replacement, use
coefHomTower_representative there, and invert the resulting quasi-isomorphism of
strict Hom towers. The identification is at every tower level and commutes with
postcomposition by I's transitions. The two sections constructions use the same
constant-to-completion scalar map, and hence give the same R action. Finally
exact evaluation on constant-ring towers preserves K-injectives. Evaluating the
same representative comparison gives integral global derived Hom into the nth
restriction of Q; independence of the input representative gives the natural
isomorphism of contravariant functors displayed below. -/
theorem coefPairingHomRepresentativeComparison (X : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E X)
    (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ) :
    (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
        (P : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ)
        (_eP : DerivedCategory.Q.obj P ≅ K)
        (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E X) ℤ)
        (_hI : I.IsKInjective)
        (_eI : DerivedCategory.Q.obj I ≅
          (coefficientSequenceDerivedRestriction.{u, u} l E X).obj (coefTraceInput l E X Q)),
        Nonempty ((coefPairingHom l E X S Q).obj (op K) ≅
          DerivedCategory.Q.obj (coefPairingHomComplex l E X P I))) ∧
    (∀ n : ℕ, Nonempty
      (coefPairingHom l E X S Q ⋙ coefTraceEvaluation l E n ≅
        coefPairingIntegralHom l E X n
          ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj
            (coefTraceInput l E X Q)))) := by sorry

end WeilConjectures
