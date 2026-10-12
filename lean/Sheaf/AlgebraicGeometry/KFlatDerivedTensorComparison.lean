/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.Algebra.Homology.KFlat

/-! # Natural computation of derived tensor on K-flat first models

Source: Stacks Project, Tag 06YH, construction of the derived tensor product.
(blueprint: lem-pc-kflat-derived-tensor-comparison).
-/

@[expose] public section

universe u w vI uI vJ uJ

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

noncomputable local instance comparisonTensor (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The derived tensor counit is a natural isomorphism on any family of K-flat first
models and any family of second models. Source: Stacks Project, Tag 06YH.
(blueprint: lem-pc-kflat-derived-tensor-comparison).

Proof: equip sheaves of modules with the recorded symmetric, closed, additive tensor
structure and functorial flat resolutions. For a K-flat complex P, the defining
acyclicity criterion implies the categorical K-flat criterion in the homotopy
category: right tensor preserves acyclic objects, and the braiding gives the left
criterion. Thus the derived tensor counit Qh(P) tensor Qh(N) to Qh(P tensor N) is
invertible for every N, by the K-flat left derivability structure. Precompose that
counit by F and G followed by the homotopy quotient. Transport along the natural
quotientCompQhIso to obtain the displayed comparison for Q. The quotient tensor
comparison identifies the right side with Q of the total tensor complex. The counit
and the quotient comparisons are natural, so the componentwise invertibility gives
an isomorphism of the curried bifunctors. -/
theorem kFlat_derivedTensor_comparison_natIso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : I ⥤ CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (G : J ⥤ CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hF : ∀ P, CochainComplex.IsKFlat (R := X.sheaf) (F.obj P)) :
    Nonempty
      (F ⋙ DerivedCategory.Q ⋙ curriedTensor (schemeDerivedCategory X) ⋙
        (Functor.whiskeringLeft J (schemeDerivedCategory X)
          (schemeDerivedCategory X)).obj (G ⋙ DerivedCategory.Q) ≅
        F ⋙ (curriedTensor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace))).map₂CochainComplex ⋙
          (Functor.whiskeringLeft J
            (CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
            (CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)).obj G ⋙
          (Functor.whiskeringRight J
            (CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
            (schemeDerivedCategory X)).obj DerivedCategory.Q) := by sorry

end AlgebraicGeometry
