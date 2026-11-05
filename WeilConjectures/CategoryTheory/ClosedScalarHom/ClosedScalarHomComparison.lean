/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Internal Hom comparison for a tensor preserving left adjoint

The five Hom equivalences of Stacks 07A6 and 08J9 give the comparison and its
restricted-evaluation normalization, independently of the choice of representatives.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ v₁ u₂ v₂
open CategoryTheory Opposite WeilConjectures
namespace CategoryTheory
namespace ClosedScalarHom
variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {H : Aᵒᵖ × A ⥤ A} {I : Bᵒᵖ × B ⥤ B}
  (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure I)
  {F : A ⥤ B} {U : B ⥤ A} (adj : F ⊣ U)
  (μ : S.tensor ⋙ F ≅ (F.prod F) ⋙ T.tensor)

end ClosedScalarHom
end CategoryTheory
