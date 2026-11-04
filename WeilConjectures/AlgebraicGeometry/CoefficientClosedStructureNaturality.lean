/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModel

/-!
# Naturality of the tensor–hom bijection of a closed tensor structure

For closed tensor data `S : CoefficientClosedStructure H`, the bijection
`Hom(T ⊗ P, Q) ≃ Hom(T, H(P, Q))` is natural in `T` by construction and natural in `P` by
`WeilConjectures.CoefficientClosedStructure.evaluation_naturality`. With a braiding, the same
holds for `Hom(P ⊗ T, Q) ≃ Hom(T, H(P, Q))`.
-/

@[expose] public section

universe a b

open CategoryTheory Opposite MonoidalCategory

namespace WeilConjectures.CoefficientClosedStructure

variable {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)

/-- The tensor–hom bijection `Hom(T ⊗ P, Q) ≃ Hom(T, H(P, Q))` is natural in `P`. -/
theorem homEquiv_tensorLeft_map_comp {T P' P Q : D} (g : P' ⟶ P)
    (φ : (@tensorRight D _ S.monoidal P).obj T ⟶ Q) :
    (S.adjunction P').homEquiv T Q ((@tensorLeft D _ S.monoidal T).map g ≫ φ) =
      (S.adjunction P).homEquiv T Q φ ≫ H.map (Prod.mkHom g.op (𝟙 Q)) := by
  let := S.monoidal
  apply ((S.adjunction P').homEquiv T Q).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    S.evaluation_naturality]
  have h : (tensorRight P).map ((S.adjunction P).homEquiv T Q φ) ≫
      (S.adjunction P).counit.app Q = φ :=
    ((S.adjunction P).homEquiv_counit (g := (S.adjunction P).homEquiv T Q φ)).symm.trans
      (Equiv.symm_apply_apply _ _)
  change (T ◁ g) ≫ φ = (((S.adjunction P).homEquiv T Q φ) ▷ P') ≫
    (H.obj (op P, Q) ◁ g) ≫ (S.adjunction P).counit.app Q
  exact (congrArg (T ◁ g ≫ ·) h).symm.trans
    (whisker_exchange_assoc ((S.adjunction P).homEquiv T Q φ) g
      ((S.adjunction P).counit.app Q))
/-- The tensor–hom bijection `Hom(P ⊗ T, Q) ≃ Hom(T, H(P, Q))`, obtained by precomposing with the
braiding, is natural in `P` and `T`. -/
theorem homEquiv_braiding_comp_naturality (β : @BraidedCategory D _ S.monoidal) {T' T P' P Q : D}
    (g : P' ⟶ P) (h : T' ⟶ T) :
    letI := S.monoidal
    ∀ φ : P ⊗ T ⟶ Q,
    (S.adjunction P').homEquiv T' Q ((β_ T' P').hom ≫ (g ⊗ₘ h) ≫ φ) =
      h ≫ (S.adjunction P).homEquiv T Q ((β_ T P).hom ≫ φ) ≫ H.map (Prod.mkHom g.op (𝟙 Q)) := by
  let := S.monoidal
  intro φ
  rw [← BraidedCategory.braiding_naturality_assoc, MonoidalCategory.tensorHom_def,
    Category.assoc]
  erw [Adjunction.homEquiv_naturality_left]
  rw [← S.homEquiv_tensorLeft_map_comp]
  rfl

end WeilConjectures.CoefficientClosedStructure
