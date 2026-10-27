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

/-- The reduction-unit tensor sections jointly detect maps from one source level.
Source: Stacks 03EK (tensor adjunction and sheafification), 0940 (quotient systems).
Proof: the nth evaluation of the quotient-system left adjoint is the ordinary
quotient of M by the nth positive uniformizer power, with quotient map induced
by the adjunction unit. This quotient map is an epimorphism of underlying module
sheaves: locally every quotient section lifts to M. After constant scalar
extension, every section locally is a sum of tensors b tensor (1 tensor x).
If two module maps agree on these sections for every site object, linearity gives
agreement on the sums and separatedness gives agreement on the original section.
Sectionwise extensionality then identifies the maps. This applies to any target
module and needs neither ramification nor any balancing comparison.
(blueprint: lem-pur-ordinary-scalar-reduction-generators). -/
theorem ordinaryScalarReduction_hom_ext (W : Scheme.{u})
    (M : scalarReductionSource l E W) (n : ℕ)
    (N : Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W)
    (f g : (pbcExtend (constantMap l E F i W)).obj
      (((ordinaryReduction l E W ⋙ systemRestriction l E W).obj M).obj (op n)) ⟶ N)
    (h : ∀ (U : W.ProEtᵒᵖ) (b : ((constants l F).ring W).obj.obj U)
      (x : M.val.obj U),
      f.val.app U (pbcTensorSection (constantMap l E F i W)
        (((ordinaryReduction l E W ⋙ systemRestriction l E W).obj M).obj (op n)) U b
        ((((ordinaryReductionAdj l E W).unit.app M ≫
          limit.π ((coefficientSequenceRestriction.{u, u} l E W).obj
            ((ordinaryReduction l E W).obj M)) (op n)).val.app U) x)) =
      g.val.app U (pbcTensorSection (constantMap l E F i W)
        (((ordinaryReduction l E W ⋙ systemRestriction l E W).obj M).obj (op n)) U b
        ((((ordinaryReductionAdj l E W).unit.app M ≫
          limit.π ((coefficientSequenceRestriction.{u, u} l E W).obj
            ((ordinaryReduction l E W).obj M)) (op n)).val.app U) x))) : f = g := by sorry

end WeilConjectures.PurStrictScalar
