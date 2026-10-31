/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportQuotientCocycleData

/-! # Universal comparison square right for quotient chain maps

Source: blueprint coefficient quotient proof, Steps 2 and 3; Stacks Tags 03EK and 06YY.
(blueprint: lem-coef-compact-support-quotient-computation-square-right).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] Padic.coefficientExtensionIdeal
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  WeilConjectures.completedIntegralCommRingSheafUnrestricted

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/- **Reduced comparison square (right).**
Source: blueprint coefficient quotient proof, Steps 2--3; Stacks Tags 06YS, 06YY and 07A6.
(blueprint: lem-coef-compact-support-quotient-computation-square-right).

The universal counit and normalized adjunction comparison identifies the specified
chain map with the corresponding derived arrow. The proof is split from the parent
comparison theorem so that the two universal squares can be established independently.
-/
/-- Universal derived computation comparison (right conjunct).

Source: blueprint coefficient quotient proof, Steps 2--3; Stacks Tags 06YS, 06YY and 07A6.
(blueprint: lem-coef-compact-support-quotient-computation-square-right).

Proof plan: use the normalized scalar-extension/quotient adjunction, the universal
computation counits and their naturality. The component formula in
`CompactSupportQuotientModuleSpec` identifies the given chain map with the ordinary
quotient (for `left`) or its adjoint transpose (for `right`); transporting through the
universal counits gives the displayed derived equality. -/
theorem compactSupportQuotient_computation_square_right (W : Scheme.{u})
    (m n : ℕ) (h : n ≤ m)
    (P : CochainComplex (scalarReductionSource.{u, u} l E W) ℤ)
    (_hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      W.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} W.ProEt) (ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E W) P)
    (_hf : ∀ i : ℤ, @SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      W.ProEt inferInstance (ProEt.topology W) inferInstance
      (integralCoefficientAbLocallyBijective.{u, u} W)
      (@HasSheafify.isRightAdjoint _ _ _ _ _ (integralCoefficientAbSheafify.{u, u} W))
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E W) (P.X i))
    (a : (compactSupportQuotientComplex l E W m).obj P ⟶
        ((proEtaleCoefficientRestrictScalars W
          (compactSupportLevelQuotient l E m n h)).mapHomologicalComplex (.up ℤ)).obj
            ((compactSupportQuotientComplex l E W n).obj P))
      (b : ((pbcExtend.{u} (compactSupportLevelSheafQuotient l E W m n h)).mapHomologicalComplex
          (.up ℤ)).obj ((compactSupportQuotientComplex l E W m).obj P) ⟶
        (compactSupportQuotientComplex l E W n).obj P)
    (hdata : (∀ i : ℤ, ∃
        (Mm : scalarReductionTarget.{u, u} l E W m)
        (Mn : scalarReductionTarget.{u, u} l E W n)
        (em : (scalarReductionExtension.{u, u} l E W m).obj (P.X i) ≅ Mm)
        (en : (scalarReductionExtension.{u, u} l E W n).obj (P.X i) ≅ Mn)
        (a₀ : Mm ⟶ (proEtaleCoefficientRestrictScalars W
          (compactSupportLevelQuotient l E m n h)).obj Mn)
        (b₀ : (pbcExtend (compactSupportLevelSheafQuotient l E W m n h)).obj Mm ⟶ Mn),
        HEq em.hom (𝟙 ((scalarReductionExtension.{u, u} l E W m).obj (P.X i))) ∧
        HEq en.hom (𝟙 ((scalarReductionExtension.{u, u} l E W n).obj (P.X i))) ∧
        HEq (a.f i) a₀ ∧ HEq (b.f i) b₀ ∧
          CompactSupportQuotientModuleSpec l E W m n h (P.X i) Mm Mn em en a₀ b₀)) :
      ((((pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E W m n h)).homEquiv
        _ _).symm (compactSupportReductionMap l E W m n h (DerivedCategory.Q.obj P))) ≫
          compactSupportQuotientComputation l E W n P =
        (pbcDerivedExtend (compactSupportLevelSheafQuotient l E W m n h)).map
            (compactSupportQuotientComputation l E W m P) ≫
          pbcComplexCounit.{u} (compactSupportLevelSheafQuotient l E W m n h)
            ((compactSupportQuotientComplex l E W m).obj P) ≫ DerivedCategory.Q.map b) := by
  sorry

end WeilConjectures
