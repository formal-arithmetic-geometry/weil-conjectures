/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenTensorQuotientData

/-! # Generator normalization for finite scalar compatibility

Source: Stacks Project, Tags 03DI and 0E8I.
(blueprint: lem-sf-open-quotient-scalar-section-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- STATEMENT-DISPUTED: `finite` is an arbitrary natural isomorphism, but the
conclusion requires it to be the specific generator-normalized comparison.
Composing a valid comparison with the automorphism `-𝟙` at an odd residue
characteristic changes the image of any nonzero extension generator, so the
conclusion cannot follow from the stated hypotheses.

The finite scalar comparison is normalized on every extension-by-zero
summand. Evaluating the comparison on the direct-sum generator gives the same
section as completed extension by zero after scalar restriction. Source: Stacks
Project, Tags 03DI and 0E8I.
(blueprint: lem-sf-open-quotient-scalar-section-compatibility). -/
theorem openQuotientScalarSectionCompatibility
    (o : IntegralOpenReduction.Operations l E j)
    (finite : ∀ n : ℕ,
      IntegralOpenReduction.finiteExtension l E j o n ⋙ scalarReductionRestriction l E X n ≅
        scalarReductionRestriction l E U n ⋙ IntegralOpenReduction.extension l E j o) :
    ∀ (n : ℕ) (M : normalizedDVRModules l E U n) (V : X.ProEt)
      (a : V ⟶ IntegralOpenReduction.openObject j)
      (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))),
      ((finite n).hom.app M).val.app (op V)
          (IntegralOpenReduction.finiteExtensionSection l E j o n M V a x) =
        IntegralOpenReduction.extensionSection l E j o
          ((scalarReductionRestriction l E U n).obj M) V a x := by
  sorry

end WeilConjectures.OpenTensorQuotient
