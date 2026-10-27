/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompactSupportQuotientCocycleData
import Sheaf.Paper.CompactSupportQuotientComputationSquareLeft
import Sheaf.Paper.CompactSupportQuotientComputationSquareRight

/-! # Universal comparison squares for quotient chain maps

Source: blueprint coefficient quotient proof, Steps 2 and 3; Stacks Tags 03EK and 06YY.
(blueprint: lem-coef-compact-support-quotient-computation-squares).
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

/-- The chain maps with the quotient and balancing formulas represent the prescribed
normalized derived quotient and its adjunct on every flat-term K-flat complex.

Source: blueprint quotient proof, Steps 1--3; Stacks Tags 06YS, 06YY and 07A6.
(blueprint: lem-coef-compact-support-quotient-computation-squares).

Proof: the ordinary integral-to-level adjunction unit is x to 1 tensor x. Thus the
termwise formula for a says that restricting a and composing with the level-m unit
gives the level-n unit, after the sectionwise restriction-composition comparison.
The given normalization of the derived integral adjunctions transports this equation
through their universal computation maps. Apply their Hom bijections and use
naturality of the exact-restriction localization comparisons: the resulting equation
is the first displayed square, since its transpose defines precisely the fixed rho.
The identity-topos K-flat pullback lemma shows that ordinary level-m extension of P
is K-flat; flat terms are preserved by extension of scalars. The quotient derived
adjunction is normalized on this complex. The formula for b, on tensors with outer
scalar 1, says that its ordinary transpose is a. Apply the normalized quotient Hom
bijection to the first square and use naturality of its counit. This gives the second
square. All identifications are the universal counits in the statement, so the
argument proves these equations for every model, rather than choosing new isomorphisms.
Equal levels and the zero complex give the same unit and balancing formulas. -/
theorem compactSupportQuotient_computation_squares (W : Scheme.{u})
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
      (compactSupportReductionMap l E W m n h (DerivedCategory.Q.obj P) ≫
          (proEtaleCoefficientRestrictScalars W
            (compactSupportLevelQuotient l E m n h)).mapDerivedCategory.map
              (compactSupportQuotientComputation l E W n P) ≫
          (proEtaleCoefficientRestrictScalars W
            (compactSupportLevelQuotient l E m n h)).mapDerivedCategoryFactors.hom.app
              ((compactSupportQuotientComplex l E W n).obj P) =
        compactSupportQuotientComputation l E W m P ≫ DerivedCategory.Q.map a) ∧
      ((((pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E W m n h)).homEquiv
        _ _).symm (compactSupportReductionMap l E W m n h (DerivedCategory.Q.obj P))) ≫
          compactSupportQuotientComputation l E W n P =
        (pbcDerivedExtend (compactSupportLevelSheafQuotient l E W m n h)).map
            (compactSupportQuotientComputation l E W m P) ≫
          pbcComplexCounit.{u} (compactSupportLevelSheafQuotient l E W m n h)
            ((compactSupportQuotientComplex l E W m).obj P) ≫ DerivedCategory.Q.map b) := by
  exact ⟨compactSupportQuotient_computation_square_left l E W m n h P _hP _hf a b hdata,
    compactSupportQuotient_computation_square_right l E W m n h P _hP _hf a b hdata⟩

end WeilConjectures
