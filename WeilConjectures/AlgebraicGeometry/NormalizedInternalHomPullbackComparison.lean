/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso

/-! # Evaluation mates of normalized derived internal Hom
Source: Stacks, Tags 08I3, 08DJ and 079U.
(blueprint: lem-pc-normalized-internal-hom-pullback-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w vC vD uC uD
open CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
noncomputable section
namespace AlgebraicGeometry
section EvaluationMate
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [MonoidalCategory C] [MonoidalCategory D]
  (H : Cᵒᵖ × C ⥤ C) (J : Dᵒᵖ × D ⥤ D)
  (F : C ⥤ D) (R : D ⥤ C) (a : F ⊣ R)
  (t : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
  (ex : ∀ A K L : C, (A ⟶ H.obj (op K, L)) ≃ (A ⊗ K ⟶ L))
  (ey : ∀ A K L : D, (A ⟶ J.obj (op K, L)) ≃ (A ⊗ K ⟶ L))
  (hx : ∀ (A A' K K' L L' : C) (p : A' ⟶ A) (b : K' ⟶ K) (c : L ⟶ L')
    (f : A ⟶ H.obj (op K, L)),
    ex A' K' L' (p ≫ f ≫ H.map (b.op, c)) = (p ⊗ₘ b) ≫ ex A K L f ≫ c)
  (hy : ∀ (A A' K K' L L' : D) (p : A' ⟶ A) (b : K' ⟶ K) (c : L ⟶ L')
    (f : A ⟶ J.obj (op K, L)),
    ey A' K' L' (p ≫ f ≫ J.map (b.op, c)) = (p ⊗ₘ b) ≫ ey A K L f ≫ c)

end EvaluationMate

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

end AlgebraicGeometry
