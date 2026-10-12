/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable

/-!
# The dual of a bounded complex of dualizable objects in the derived category

Let `A` be a braided monoidal closed Grothendieck abelian category with functorial flat
resolutions, and `P` a bounded complex of dualizable objects of `A`. Then `Q P` and
`Q P^∨` form an exact pairing in `D(A)`, where `P^∨` is the termwise dual complex
(`CochainComplex.rightDual`): the dual of `Q P` in the derived category is computed termwise
(`DerivedCategory.nonempty_exactPairing_Q_obj_rightDual`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]

local instance : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A

/-- **The derived dual of a bounded complex of dualizable objects is the termwise dual**: for a
bounded complex `P` of dualizable objects, `Q P` and `Q P^∨` form an exact pairing in `D(A)`,
`P^∨` being the termwise dual complex. -/
theorem nonempty_exactPairing_Q_obj_rightDual (P : CochainComplex A ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] [∀ n, HasRightDual (P.X n)] :
    Nonempty (ExactPairing (Q.obj P) (Q.obj P.rightDual)) := by
  let _ := CochainComplex.exactPairingRightDual P a b
  let H := HomotopyCategory.quotient A (.up ℤ)
  have hP : ∀ n, IsDualizable (P.X n) := fun n ↦ ⟨inferInstance⟩
  have hP' : ∀ n, IsDualizable (P.rightDual.X n) := fun n ↦
    ⟨{ rightDual := P.X (-n)
       exact := (BraidedCategory.exactPairing_swap (P.X (-n)) (P.X (-n))ᘁ :) }⟩
  let X : (HomotopyCategory.quasiIso A (.up ℤ)).kFlat.FullSubcategory :=
    ⟨H.obj P, (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (CochainComplex.kFlat_of_bounded_of_flat P a b (fun n ↦ (hP n).flat))⟩
  let Y : (HomotopyCategory.quasiIso A (.up ℤ)).kFlat.FullSubcategory :=
    ⟨H.obj P.rightDual, (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (CochainComplex.kFlat_of_bounded_of_flat P.rightDual (-b) (-a) (fun n ↦ (hP' n).flat))⟩
  let _ : ExactPairing ((ObjectProperty.ι _).obj X) ((ObjectProperty.ι _).obj Y) :=
    ExactPairing.map H P P.rightDual
  let _ : ExactPairing X Y := ExactPairing.ofFullyFaithful (ObjectProperty.ι _) X Y
  let _ := Functor.Monoidal.ofLaxMonoidal (kFlatQh A)
  let e : ExactPairing ((kFlatQh A).obj X) ((kFlatQh A).obj Y) := ExactPairing.map (kFlatQh A) X Y
  exact ⟨@exactPairingCongr _ _ _ _ _ ((kFlatQh A).obj X) _ ((kFlatQh A).obj Y) e
    ((quotientCompQhIso A).app P).symm ((quotientCompQhIso A).app P.rightDual).symm⟩

end DerivedCategory
