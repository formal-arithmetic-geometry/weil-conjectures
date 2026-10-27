/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedPullbackTensorConstraints

/-! Uniqueness of the integral unit comparison.

Source: Stacks Project, Tag 07A4, label lemma-pullback-tensor-product; cancellation
with the tensor unitors in the integral constructible category.
(blueprint: lem-pur-pullback-tensor-integral-unit-coherence-uniqueness)

Applying coherent reduction to either pair of unit equations and cancelling the
invertible comparison and unitor identifies the two candidate unit maps.
Faithfulness of coherent reduction then reflects equality of the original maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The two integral unit equations determine their comparison isomorphism.
Source: Stacks Project, Tag 07A4; unit cancellation after coherent reduction.
(blueprint: lem-pur-pullback-tensor-integral-unit-coherence-uniqueness)
-/
theorem canonicalIntegralPullbackTensor_unit_unique {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (ε δ : ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj
      ((@pullbackTensorIntegralUnit l _ E _ _ _ Y hY)) ≅
        (@pullbackTensorIntegralUnit l _ E _ _ _ X hX))
    (hε : ∀ M : sfIntegralConstructibleCategory l E Y,
      (((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY)
        ((@pullbackTensorIntegralUnit l _ E _ _ _ Y hY)) M).hom ≫
        ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map
          (Prod.mkHom ε.hom (𝟙 _)) ≫
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ X hX)
          (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)).hom =
      ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ Y hY) M).hom) ∧
      (((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M
        ((@pullbackTensorIntegralUnit l _ E _ _ _ Y hY))).hom ≫
        ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map
          (Prod.mkHom (𝟙 _) ε.hom) ≫
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ X hX)
          (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)).hom =
      ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ Y hY) M).hom))
    (hδ : ∀ M : sfIntegralConstructibleCategory l E Y,
      (((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY)
        ((@pullbackTensorIntegralUnit l _ E _ _ _ Y hY)) M).hom ≫
        ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map
          (Prod.mkHom δ.hom (𝟙 _)) ≫
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ X hX)
          (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)).hom =
      ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ Y hY) M).hom) ∧
      (((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M
        ((@pullbackTensorIntegralUnit l _ E _ _ _ Y hY))).hom ≫
        ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map
          (Prod.mkHom (𝟙 _) δ.hom) ≫
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ X hX)
          (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)).hom =
      ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ Y hY) M).hom)) :
    ε = δ := by sorry

end WeilConjectures
