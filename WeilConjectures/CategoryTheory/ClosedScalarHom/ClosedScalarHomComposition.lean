/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
/-! # Composition of the five closed-Hom bijections -/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ v₁ u₂ v₂ u₃ v₃
open CategoryTheory Opposite WeilConjectures
namespace CategoryTheory.ClosedScalarHom
variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {C : Type u₃} [Category.{v₃} C]
  {H : Aᵒᵖ × A ⥤ A} {I : Bᵒᵖ × B ⥤ B} {J : Cᵒᵖ × C ⥤ C}
  (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure I)
  (V : CoefficientClosedStructure J)
  {F : A ⥤ B} {U : B ⥤ A} (adj : F ⊣ U)
  {G : B ⥤ C} {W : C ⥤ B} (adj' : G ⊣ W)
  (μ : S.tensor ⋙ F ≅ (F.prod F) ⋙ T.tensor)
  (ν : T.tensor ⋙ G ≅ (G.prod G) ⋙ V.tensor)
  (μ₀ : S.tensor ⋙ (F ⋙ G) ≅ ((F ⋙ G).prod (F ⋙ G)) ⋙ V.tensor)
  (hμ : ∀ X K, μ₀.hom.app (X, K) =
    G.map (μ.hom.app (X, K)) ≫ ν.hom.app (F.obj X, F.obj K))

end CategoryTheory.ClosedScalarHom
