/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedPullbackTensorConstraints

/-! Existence of the integral unit comparison.

Source: Stacks Project, Tag 07A4, label lemma-pullback-tensor-product; the
integral coefficient-level unit coherence construction.
(blueprint: lem-pur-pullback-tensor-integral-unit-coherence-existence)

The normalized coherent system unit comparison is lifted through the fully
faithful integral reduction.  Its two system-level unitor equations transport
along the reduction, tensor, pullback, and unit counits to the displayed
integral equations.
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

/-- Existence half of integral pullback tensor unit coherence.
Source: Stacks Project, Tag 07A4; normalized coefficient-level unit comparison.
(blueprint: lem-pur-pullback-tensor-integral-unit-coherence-existence)
-/
theorem canonicalIntegralPullbackTensor_unit_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃ ε : ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj
      ((@pullbackTensorIntegralUnit l _ E _ _ _ Y hY)) ≅
        (@pullbackTensorIntegralUnit l _ E _ _ _ X hX),
      ∀ M : sfIntegralConstructibleCategory l E Y,
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
          ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ Y hY) M).hom) := by sorry

end WeilConjectures
