/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocallyFiniteAdicCompactSupportData

/-! # Components of the normalized integral presentation pullback square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]

/--
The component at each pro-etale test object of the normalized integral-map square.

Proof source: Bhatt--Scholze, Lemma 6.8.2 and Section 6.8. The finite constant and
residue formulas identify both component maps pointwise; the inverse-limit comparison
then gives equality of the displayed component ring homomorphisms.
(blueprint: lem-sf-native-completed-coefficient-integral-map-square-component)
-/
theorem coefficient_presentation_integralMap_pull_square_component
    [G : NativeGeometry.{u} l]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l)
    (C : ∀ T : Scheme.{u}, CoefficientPresentation l T E i)
    {U V : Scheme.{u}} (g : U ⟶ V) (W : U.ProEtᵒᵖ) :
      (((PurCompactSupport.completed l E).pull g).hom ≫
          (C U).integralMap l U).hom.app W =
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
            ((C V).integralMap l V) ≫
          ((nativeCoefficients l).pull g).hom).hom.app W := by
  sorry

end WeilConjectures.LocallyFiniteAdicCompactSupport
