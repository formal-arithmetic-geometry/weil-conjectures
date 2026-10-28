/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E6
-/
module

public import Sheaf.SixFunctors.IntegralDualizingSystemTraceData

/-! # Compatibility of the finite exceptional counit family

Source: prop-coef-integral-dualizing, paragraph 2, and finite coefficient counit change.
(blueprint: lem-coef-system-finite-counit-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The prescribed finite trace word. It is a morphism only at the specified
finite level and makes no assertion that it lifts to a system morphism.
Source: prop-coef-integral-dualizing, paragraph 2.
(blueprint: lem-coef-system-finite-counit-compatibility). -/
def integralDualizingFiniteTraceWord
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (Q : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n)
    (c : G.openModules.mapDerivedCategory ⋙ G.properModules.rightDerivedFunctor ≅
      ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) (finiteDualizingCompactification D X).i ⋙
        ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) (finiteDualizingCompactification D X).g)
    (eU : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj
        G.baseTensors.systemClosed.monoidal.tensorUnit ≅
      (finiteDualizingRealization l E (Spec (.of D.k)) n).obj
        (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k))))
    (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj
        (G.properModules.rightDerivedFunctor.obj
          (G.openModules.mapDerivedCategory.obj (coefTraceInput l E X Q))) ⟶
      (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj
        G.baseTensors.systemClosed.monoidal.tensorUnit :=
  (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).map
      (c.hom.app (coefTraceInput l E X Q)) ≫
    (compactSupportSystemEvaluation l E (finiteDualizingCompactification D X) n).hom.app
      (coefTraceInput l E X Q) ≫
    (sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
      (Padic.coefficientExtensionRing l E (n + 1))).map (eQ n).hom ≫
    integralDualizingFiniteSystemCounit D l E X n ≫ (eU n).inv

/-- The finite counits, with the actual support and unit identifications, commute
with adjacent quotient arrows. This asserts no lift to the derived system category.

Source: prop-coef-integral-dualizing, paragraph 2; the counit identity in
lem-coef-finite-dualizing and the native compact-support evaluation comparison.
(blueprint: lem-coef-system-finite-counit-compatibility).

Proof: identify the ordinary open and proper functors with their native varying-ring
models using openRestriction and properRestriction. Restriction to constant integral
scalars is fully faithful on quotient module sheaves: locally the quotient scalar
map is surjective, so integral-linear maps between quotient modules are quotient-linear.
These identifications retain the actual underlying sheaf maps. Exact restriction and
the derived composition comparisons then give the natural support comparison c.
The tensor model identifies the base monoidal unit with the coefficient ring complex
in degree zero, by the unit universal property. Evaluate this one system isomorphism
and use the generator-normalized finiteDualizingIntrinsicUnit to obtain eU. Thus the
transitions of the evaluated unit are the genuine quotient maps.
For the counit square, expand integralDualizingFiniteTraceWord. Naturality moves c
past the source transition. The native evaluation square identifies the next factor
with the compact-support image of the quotient-semilinear transition of Q. Substitute
hQ to replace that transition by the scalar adjunct of the finite dualizing comparison.
Transport the resulting word to the ordinary etale site by finiteDualizingOrigin and
the canonical compact-support site comparison. The counit equation in
finiteDualizingCoefficientComparisons cancels the compact-support coefficient mate.
Naturality of the scalar-adjunction unit turns the remaining composite into the
quotient map of coefficient units after the old counit. The unit normalization of eU
identifies this with the actual target system transition. Transport back to intrinsic
coefficients and compose with the inverse eU maps, obtaining exactly the displayed
square. No equality of whole-system maps is inferred from their evaluations.
The argument remains valid for the empty scheme, zero complexes, and the residue
level n=0, and uses no flatness of a quotient map. -/
theorem integralDualizingFiniteCounit_compatible (hl : l ≠ D.p)
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (Q : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n)
    (hQ : ∀ {m n : ℕ} (h : n ≤ m),
      (coefficientSequenceDerivedTransition l E X h).app (coefTraceInput l E X Q) ≫
          (normalizedDVRRes l E X h).map (eQ n).hom =
        (eQ m).hom ≫
          (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
            (integralDualizingFiniteComparison l E D X hl h)) :
    ∃ (c : G.openModules.mapDerivedCategory ⋙ G.properModules.rightDerivedFunctor ≅
      ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) (finiteDualizingCompactification D X).i ⋙
        ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) (finiteDualizingCompactification D X).g)
      (eU : ∀ n : ℕ,
        (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj
          G.baseTensors.systemClosed.monoidal.tensorUnit ≅
        (finiteDualizingRealization l E (Spec (.of D.k)) n).obj
          (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)))),
      ∀ n : ℕ,
        integralDualizingFiniteTraceWord D l E X S G Q eQ c eU (n + 1) ≫
            (coefficientSequenceDerivedTransition l E (Spec (.of D.k))
              (Nat.le_succ n)).app G.baseTensors.systemClosed.monoidal.tensorUnit =
          (coefficientSequenceDerivedTransition l E (Spec (.of D.k))
              (Nat.le_succ n)).app
              (G.properModules.rightDerivedFunctor.obj
                (G.openModules.mapDerivedCategory.obj (coefTraceInput l E X Q))) ≫
            (normalizedDVRRes l E (Spec (.of D.k)) (Nat.le_succ n)).map
              (integralDualizingFiniteTraceWord D l E X S G Q eQ c eU n) := by sorry

end WeilConjectures
