/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P7
-/
module

public import Sheaf.CategoryTheory.NativeHomSourceShiftData

/-! # The degree-one recurrence for the raw source-Hom mates

Source: Stacks Project, Tags 08J9 and 08JC.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe v d
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.ProEtale

variable {D : Type d} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]

/-- Increasing the opposite source shift by one introduces the sign `(-1)^m`.
Source: Stacks Project, Tags 08J9 and 08JC, tensor-Hom adjunction and total-tensor signs;
the explicit mate calculation is the degree-one case of the source-Hom shift calculation
(blueprint: lem-sf-native-hom-source-shift-successor).

Proof: put T_K = tensorLeft K. The defining left map of the raw source mate is
c_K^r followed by the inverse of t_K^r, where c and t are the argument and parameter
tensor-shift comparisons. Compare the direct map for r = -(m+1) with the two left
maps for r = -m and r = -1. Use the addition laws for c and t to combine their
successive copies. Exactly one interchange of the parameter and argument shifts
is required. CommShift₂Int.comm with these parameters contributes
(-1)^((-m)*(-1)) = (-1)^m; its shiftComm term restores the order of the two
opposite shifts. Taking right-adjoint mates reverses the left compositions.
The shift-adjunction triangle identities cancel the intervening unit and counit.
The remaining parameter comparison is precomposition by the opposite
shiftFunctorAdd hom, and the remaining output comparison is shiftFunctorAdd.inv.
Transport -(-m)=m and -(-1)=1 as in siteHomOppositeSourceShift. This gives the
four-factor composite below with exactly the displayed sign. All steps use only
shift addition and the tensor interchange identity, hence apply to negative m as
well. For m=0 the tensor zero unitors cancel, consistently with the unit law. -/
theorem siteHom_opposite_source_shift_successor (M : D) (m : ℤ) (X : Dᵒᵖ) :
    (siteHomOppositeSourceShift X.unop (m + 1)).hom.app M =
      m.negOnePow •
        ((MonoidalClosed.internalHom.flip.obj M).map
            ((shiftFunctorAdd Dᵒᵖ m 1).hom.app X) ≫
          (siteHomOppositeSourceShift (X⟦m⟧).unop 1).hom.app M ≫
          ((siteHomOppositeSourceShift X.unop m).hom.app M)⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd D m 1).inv.app ((ihom X.unop).obj M)) := by sorry

end AlgebraicGeometry.ProEtale
