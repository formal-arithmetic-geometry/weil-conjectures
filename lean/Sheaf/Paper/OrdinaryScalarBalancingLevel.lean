module

public import Sheaf.Paper.NativeConstantSupportModel

/-! # Ordinary scalar reduction at one quotient level

Source: Stacks 03EK and 0940.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] WeilConjectures.PurStrictScalar.ordinaryReduction
  WeilConjectures.PurStrictScalar.ordinaryReductionAdj
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- At a single quotient level the scalar reassociation has its prescribed tensor formula.
Source: Stacks 03EK (tensor/restriction adjunction), 0940 (quotient systems).
Proof: evaluation of the quotient-system left adjoint identifies its unit with the
quotient map M to M modulo the source uniformizer power. The ramification equality
identifies its extension to B with the retained target uniformizer ideal. Tensor
associativity and the quotient tensor equivalence therefore give an isomorphism
B tensor_A (M modulo t^(n+1)) to (Bhat tensor_Ahat M) modulo v^(e(n+1)).
Send b tensor (1 tensor x) to 1 tensor (b tensor x). The inverse is the reverse
reassociation, using the quotient ideal equality; both composites are identity on
local tensor generators. Apply module sheafification, whose universal property
preserves these inverse maps and the formula. Transport the quotient adjunction
unit by uniqueness of left adjoints to obtain exactly the unit appearing here.
This only asserts existence separately for M,n; horizontal and module naturality
are proved by the consuming tower construction. Positivity ensures the retained
exponent is positive, and the zero module and empty site object cause no exception.
(blueprint: lem-pur-ordinary-scalar-balancing-level). -/
theorem ordinaryScalarBalancingLevel_exists (W : Scheme.{u}) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) :
    let ηE (M : scalarReductionSource l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
        (x : M.val.obj U) :=
      (((ordinaryReductionAdj l E W).unit.app M ≫
        limit.π ((coefficientSequenceRestriction.{u, u} l E W).obj
          ((ordinaryReduction l E W).obj M)) (op n)).val.app U) x
    let ηF (M : scalarReductionSource l F W) (n : ℕ) (U : W.ProEtᵒᵖ)
        (x : M.val.obj U) :=
      (((ordinaryReductionAdj l F W).unit.app M ≫
        limit.π ((coefficientSequenceRestriction.{u, u} l F W).obj
          ((ordinaryReduction l F W).obj M)) (op n)).val.app U) x
    ∀ (M : scalarReductionSource l E W) (n : ℕ),
    ∃ β : (pbcExtend (constantMap l E F i W)).obj
        (((ordinaryReduction l E W ⋙ systemRestriction l E W).obj M).obj (op n)) ≅
      (((ordinaryReduction l F W ⋙ systemRestriction l F W).obj
        ((pbcExtend (completedCoefficientMap l E F i W)).obj M)).obj
          (op (e * (n + 1) - 1))),
      ∀ (U : W.ProEtᵒᵖ)
        (b : ((constants l F).ring W).obj.obj U) (x : M.val.obj U),
        (β.hom.val.app U)
            (pbcTensorSection (constantMap l E F i W)
              ((((ordinaryReduction l E W ⋙ systemRestriction l E W)).obj M).obj (op n)) U b
              (ηE M n U x)) =
          ηF
            ((pbcExtend (completedCoefficientMap l E F i W)).obj M)
            (e * (n + 1) - 1) U
            (pbcTensorSection (completedCoefficientMap l E F i W) M U
              (((integralConstantToCompletionOfUniverses l F W).hom.app U) b) x) := by
  sorry

end WeilConjectures.PurStrictScalar
