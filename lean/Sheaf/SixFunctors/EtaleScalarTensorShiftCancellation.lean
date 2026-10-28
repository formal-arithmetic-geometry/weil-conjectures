/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.SixFunctors.EtaleHomComparisonModels

/-! # Scalar tensor comparison and cancellation of opposite shifts -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CategoryTheory.Pretriangulated.Opposite Opposite
namespace AlgebraicGeometry.Etale

/-- The normalized scalar tensor comparison respects cancellation of opposite shifts.
Source: Stacks Project, Tags 06YY, 07A4 and 08JC; the tensor-balancing calculation
in the proof of `lem-coef-etale-hom-transpose-exact-comm-shift-core`.

Choose flat-term K-flat representatives P and Q for K and L. Their shifts are
again flat-term K-flat. Use `DerivedCategory.commShiftTensorLeft_eq` and
`DerivedCategory.commShiftTensorRight_eq` to identify the tensor shifts with
cochain reindexing on these representatives. The counit normalization of the
binary comparison
identifies it with ordinary scalar balancing on these representatives. The scalar
shift is the adjoint mate of restriction's termwise shift, so its counit equation
identifies it with termwise scalar extension and reindexing. Both sides are then
the same balancing map on each total-complex summand: the tensor signs of the
shifts by -n and n occur in exactly the order in the displayed cancellation.
Localize this equality, using the two counit equations, and transport along the
representative isomorphisms by naturality in K and L. This argument involves no
internal Hom or evaluation map, and requires no flatness of B over A.
(blueprint: lem-coef-etale-scalar-tensor-shift-cancellation) -/
theorem etaleHomTensorComparison_shiftCancellation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (K L : DerivedCategoryModule A X) (n : ℤ) :
    letI := etaleHomScalarCommShift X φ
    ((derivedTensor (ModuleCat.{u + 1} B) X).map
        (((scalarExtension φ X).commShiftIso (-n)).hom.app K)).app
          ((scalarExtension φ X).obj (L⟦n⟧)) ≫
      ((derivedTensor (ModuleCat.{u + 1} B) X).obj
        (((scalarExtension φ X).obj K)⟦-n⟧)).map
          (((scalarExtension φ X).commShiftIso n).hom.app L) ≫
      etaleHomTensorShiftCancellation (ModuleCat.{u + 1} B) X
        ((scalarExtension φ X).obj K) ((scalarExtension φ X).obj L) n ≫
      (etaleHomTensorComparison X φ K L).hom =
    (etaleHomTensorComparison X φ (K⟦-n⟧) (L⟦n⟧)).hom ≫
      (scalarExtension φ X).map
        (etaleHomTensorShiftCancellation (ModuleCat.{u + 1} A) X K L n) := by
  sorry

end AlgebraicGeometry.Etale
