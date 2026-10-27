/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
public import Sheaf.Paper.CompactSupportNativeSystemEvaluation

/-! # Strict coefficient reduction for open image

Source: Stacks 07A6, 0941; Bhatt--Scholze 6.7.6--6.7.7.
(blueprint: lem-strict-coefficient-open-reduction). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}}

/-- Native evaluation in the finite ringed open-image presentation.
Source: Stacks 03DI, 0D6E (blueprint: lem-strict-coefficient-open-reduction). -/
def strictCoefficientOpenEvaluation (f : X ⟶ Y) [IsOpenImmersion f] (n : ℕ) :
    ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f ⋙
      coefficientSequenceDerivedEvaluation l E Y n ≅
    coefficientSequenceDerivedEvaluation l E X n ⋙
      (openExtension (finite l E (n + 1) (Nat.le_add_left 1 n)) f).mapDerivedCategory := by
  have := sfIntrinsicExtensionByZero_additive f
    (Padic.coefficientExtensionRing l E (n + 1))
  have := (sfIntrinsicExtensionByZero_exact f
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  have := (sfIntrinsicExtensionByZero_exact f
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  let e := ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f n ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryNatIso
      (compactSupportOpenModel f (Padic.coefficientExtensionRing l E (n + 1))))
  exact e ≪≫ Functor.isoWhiskerLeft _
    (Functor.mapDerivedCategoryNatIso (finiteOpenIso l E n f)).symm

/-- Reduction commutes with the open factor as a map of whole strict systems,
with the scalar-adjunction mate at every finite coordinate.

Source: Stacks 03DI, 0E8I, 0941; Bhatt--Scholze 6.7.6--6.7.7;
the second arrow of the Isomorphism paragraph in the blueprint proof of
`sk-prop-scalar-six-compact-support`.
(blueprint: lem-strict-coefficient-open-reduction).

Proof: Choose flat-term K-flat representatives for the completed input. Extension by zero is exact
and preserves these representatives: it is identity on the open and zero on its complement.
Tensoring this extension with the entire quotient-ring diagram agrees with extension of the
quotient-tensor diagram. The sectionwise comparison sends each tensor generator to the same tensor
in its extension summand. It commutes with every quotient transition because reduction of the
coefficient commutes with that formula. Descend this natural map through homotopies and
quasi-isomorphisms, and use the reductionModel identifications to obtain the displayed strict-system
map. At each finite level its open-adjunction transpose is the scalar-restricted open unit. This is
precisely the mate defining openComparison. The prescribed open evaluation is normalized by that
same unit; the reduction unit normalization fixes both finiteReductionIso factors. Thus the
displayed equation follows before any total limit is taken. This argument works for every ambient
input, without a completeness hypothesis.
The zero input, empty scheme, identity morphism and n=0 (exponent one) obey the same
unit, tensor and quotient equations.
-/
theorem strictCoefficientOpenReduction (f : X ⟶ Y) [IsOpenImmersion f]
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SY : CoefficientDerivedSystemCalculus l E Y) :
    ∃ β : (openExtension (completed l E) f).mapDerivedCategory ⋙ SY.reduction ⟶
        SX.reduction ⋙ ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f,
      ∀ (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ),
        (coefficientSequenceDerivedEvaluation l E Y n).map (β.app K) ≫
            (strictCoefficientOpenEvaluation l E f n).hom.app (SX.reduction.obj K) =
          ((SY.reductionEvaluation n).hom.app
              ((openExtension (completed l E) f).mapDerivedCategory.obj K) ≫
            (finiteReductionIso l E Y n).inv.app
              ((openExtension (completed l E) f).mapDerivedCategory.obj K)) ≫
            (openComparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) f).app K ≫
            ((openExtension (finite l E (n + 1) (Nat.le_add_left 1 n)) f).mapDerivedCategory).map
              ((finiteReductionIso l E X n).hom.app K ≫
                (SX.reductionEvaluation n).inv.app K) := by
  sorry

end WeilConjectures
