/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportScalarShiftStructures

/-! # ScalarLimitConstraintShift

Source: Stacks Project; canonical scalar shifts
(blueprint: lem-pur-scalar-limit-constraint-shift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F) (W : Scheme.{u})
/-- Shift squares for the normalized scalar limit constraints.
Source: Stacks Tags 05SU, 06YU, 0941, 099L; Steps 6--8 of
lem-pur-compact-support-scalar-shift-normalization.
(blueprint: lem-pur-scalar-limit-constraint-shift).

Proof: shift a strict K-injective tower resolution; it remains K-injective.
The resolution arrow acts diagonally on the two Roos coordinates, and the
augmentation has zero extra coordinate, so the signed Roos shift agrees with
the canonical total-derived-limit shift. The arithmetic selection and block sum
are degree-zero maps and commute with the shift termwise, with the same sign on
the extra coordinate. Tensor/product comparison is determined by its projections;
each projection commutes with degree-zero tensor and shift. For scalarCompletion,
use its equation on all complex counits: ordinary balancing is degreewise and
commutes with shifts; the universal scalar counit fixes the descended comparison
uniquely. Its zero extra Roos coordinate stays zero under the cone sign. Finally
scalarSupportLimit consists of unit-normalized derived composition and exact
restriction comparisons. The same resolution computation gives its square.
For the final total-limit square, whisker the strict mate square of Step 5 by
total limit, then compose with the tensor/limit square and inverse arithmetic
restriction square. Insert the canonical associators: their components are
identities, so the composite component is exactly scalarLimitArrow. The intermediate
shift maps cancel, giving the stated equation. This last clause requires e≥1.
All forward-constraint arguments apply to every integer and to e=0 as well: no invertibility of
arithmetic restriction is needed for its forward shift equation. -/
theorem scalarLimitConstraintShift {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) (e : ℕ) :
    @NatTrans.CommShift _ _ _ _ _ _ (scalarCompletion l E F i Y).hom ℤ _ _ _
      inferInstance (scalarCompletionTargetCommShift l E F i Y) ∧
    NatTrans.CommShift (scalarLimitTensor l E F i Y).hom ℤ ∧
    NatTrans.CommShift (scalarLimitRestriction l E Y e) ℤ ∧
    @NatTrans.CommShift _ _ _ _ _ _ (scalarSupportLimit l E c S).hom ℤ _ _ _
      (by
        letI := scalarSupportCommShift l E c S
        letI := constantRestrictionCommShift l E Y
        exact Functor.CommShift.comp (A := ℤ) _ _)
      (by
        letI := supportCommShift l E c S
        exact Functor.CommShift.comp (A := ℤ) _ _) ∧
    (∀ (S' : CoefficientDerivedSystemCalculus.{u, u} l F X)
      (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
      (K : DerivedCategory (scalarReductionSource l E X)) (r : ℤ),
      scalarLimitArrow l E F i c S S' e he hepos (K⟦r⟧) ≫
          ((pbcDerivedExtend (completedCoefficientMap l E F i X) ⋙
            support l F c S' ⋙ scalarLimit l F Y).commShiftIso r).hom.app K =
        ((support l E c S ⋙ scalarLimit l E Y ⋙
          baseTensor l E F i Y).commShiftIso r).hom.app K ≫
          (scalarLimitArrow l E F i c S S' e he hepos K)⟦r⟧') := by sorry

end WeilConjectures.PurStrictScalar
