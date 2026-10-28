/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.WeilSheaf.CanonicalCoefficientWeilCohomology

/-! # Normalized realization of the coefficient Weil heart -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.ConstantPurityFrobenius

attribute [local instance 1100] CategoryTheory.instOverClass

namespace WeilConjectures.NativeCoefficientCohomology

variable (P : PurityFiniteSetting.{u})
  (X₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

local instance nativeHeartStructureOver : X₀.hom.IsOver (Spec (.of P.field.k₀)) := by
  constructor
  dsimp only [autoParam]
  change X₀.hom ≫ 𝟙 _ = X₀.hom
  rw [Category.comp_id]

/-- Realization of the degree-zero coefficient Weil heart, normalized on root lines
and the counit of exceptional inverse image.

Source: BS 6.8.14--6.8.15; current blueprint,
`cor-coef-verdier-weil-equivariance.proof.md`, exceptional-adjunction paragraph, and
`lem-pur-constant-purity-frobenius-square`, root-line normalization.
(blueprint: lem-sf-native-coefficient-heart-comparison)

Proof: restrict the exact normalized ordinary realization to the standard heart,
transporting the specified coefficient closure and geometric closure. Exact geometric
Frobenius pullback and its realization comparison give a functor on the fixed-pair
hearts. Full faithfulness and essential surjectivity follow from the ordinary heart
equivalence, transporting the invertible Frobenius map and its intertwining equation.
For the exceptional comparison, realize the coefficient adjunction counit, using the
counit-normalized compact-support comparison and scalar-unit normalization at the
arithmetic point. Transposition identifies its Frobenius with the inverse-exchange
right mate followed by the constant Frobenius. Apply standard cohomology; exactness
identifies this with canonicalCoefficientWeilCohomology. Exact native forgetting
computes native homologySheaf. Uniqueness of right adjoints gives the comparison for any supplied J.
On an unshifted coefficient root line, integral realization sends the compatible root
tower to the native cyclotomic line. Rationalization, scalar extension and the tensor
unit comparison give the native Tate sheaf tensor the native constant sheaf. These
normalizations intertwine Frobenius before taking the heart. No shifted Tate complex
or assertion about its nonzero-degree cohomology is involved in this heart comparison.
At d=0 use the scalar unit; on the empty scheme all these are zero objects. -/
theorem native_coefficient_heart_comparison
    (c₀ : Compactification X₀.hom)
    (S : systems P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar X₀)
    [Fact (ringChar P.field.k₀ ≠ P.coefficients.l)] :
    ∃ E : sfCommonStageWeilSheaf P.field P.coefficients.l P.coefficients.different
        X₀ P.coefficients.Qbar ⥤ WeilSheaf P.field.k₀ P.coefficients.l X₀.left,
      E.IsEquivalence ∧
      (∀ (J : WeilComplex P.field.k₀ P.coefficients.l (Spec (.of P.field.k₀)) ⥤
          WeilComplex P.field.k₀ P.coefficients.l X₀.left)
        (adj : WeilComplex.derivedLowerShriek P.field.k₀ P.coefficients.l X₀.hom ⊣ J)
        (n : ℤ),
        Nonempty ((WeilComplex.homologySheaf n).obj
            (J.obj (WeilSheaf.toComplex.obj
              (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l
                (Spec (.of P.field.k₀))))) ≅
          E.obj ((canonicalCoefficientWeilCohomology P X₀ n).obj
              (exceptionalConstant P X₀ c₀ S)))) ∧
      (∀ d : ℕ, Nonempty (E.obj
          (FrobeniusCoefficientTwists.commonWeilSheaf P.field P.coefficients.l
            P.coefficients.different X₀ P.coefficients.Qbar (d : ℤ)) ≅
        (WeilSheaf.tateTwistSheaf P.field.k₀ P.coefficients.l X₀.left d).tensorObj
          (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l X₀.left)
          (WeilSheaf.isLisse_tateTwistSheaf P.field.k₀ P.coefficients.l X₀.left d))) := by
  sorry

end WeilConjectures.NativeCoefficientCohomology
