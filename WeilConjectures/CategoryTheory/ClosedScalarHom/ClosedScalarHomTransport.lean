/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
import all WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
/-! # Transport of the normalized closed-Hom comparison along adjoint isomorphisms -/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u₁ v₁ u₂ v₂
open CategoryTheory Opposite WeilConjectures
namespace CategoryTheory.ClosedScalarHom
variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {H : Aᵒᵖ × A ⥤ A} {I : Bᵒᵖ × B ⥤ B}
  (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure I)
  {F F' : A ⥤ B} {U U' : B ⥤ A} (adj : F ⊣ U) (adj' : F' ⊣ U')
  (d : U' ≅ U) (c : F ≅ F')
  (hc : ∀ X N (f : F'.obj X ⟶ N),
    adj.homEquiv X N (c.hom.app X ≫ f) = adj'.homEquiv X N f ≫ d.hom.app N)
  (μ : S.tensor ⋙ F ≅ (F.prod F) ⋙ T.tensor)
  (ν : S.tensor ⋙ F' ≅ (F'.prod F') ⋙ T.tensor)
  (hμ : ∀ X K, μ.hom.app (X, K) ≫
    T.tensor.map (Prod.mkHom (c.hom.app X) (c.hom.app K)) =
      c.hom.app (S.tensor.obj (X, K)) ≫ ν.hom.app (X, K))

end CategoryTheory.ClosedScalarHom
