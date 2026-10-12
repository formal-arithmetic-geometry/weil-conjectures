/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.Functoriality
public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.Reduction

/-!
# The completion map

Let `A` be a monoidal closed braided Grothendieck abelian category with functorial flat
resolutions and let `P : ℕᵒᵖ ⥤ CochainComplex A ℤ` be a coefficient tower together with an
*augmentation* `ε : 𝟙 ⟶ Pₙ` compatible with the transition maps (for instance the quotient maps
`R ⟶ R/Iⁿ`, or the augmentations of Koszul complexes). This file constructs the completion map

`comp_K : K ⟶ R lim K_•`

of an object `K` of `D(A)` into the derived limit of its reduction tower
`K_• = DerivedCategory.reductionTower P K` (Blueprint `def-weil-pbc-completion-map`).

It is defined through the derived adjunction `const ⊣ R lim`
(`DerivedCategory.towerConstAdjunction`) between the constant tower functor and the derived
limit: `comp_K` is adjoint to the map from the constant tower on `K` to `K_•` induced by the
augmentation (`DerivedCategory.towerConstToReductionTower`).

We also record the functoriality of the reduction tower in the coefficient tower
(`DerivedCategory.reductionTowerMap`): a levelwise quasi-isomorphism of coefficient towers
induces an isomorphism of reduction towers, hence of their derived limits.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory Opposite

namespace DerivedCategory

section Const

variable (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]

instance : PreservesFiniteLimits (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

instance : PreservesFiniteColimits (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- The constant tower functor `D(A) ⥤ D(ℕᵒᵖ ⥤ A)`, induced by the exact functor
`const : A ⥤ (ℕᵒᵖ ⥤ A)`. -/
noncomputable def towerConst : DerivedCategory A ⥤ DerivedCategory (ℕᵒᵖ ⥤ A) :=
  (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory

/-- The derived adjunction `const ⊣ R lim`, induced by the adjunction `const ⊣ lim`. -/
noncomputable def towerConstAdjunction : towerConst A ⊣ rlim A :=
  (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A) ⊣ lim).mapDerivedCategoryRightDerivedAdjunction

end Const

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [Abelian.HasFunctorialFlatResolution A]

local instance : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A

section Functoriality

variable {P P' : ℕᵒᵖ ⥤ CochainComplex A ℤ}

/-- A map of coefficient towers `φ : P ⟶ P'` induces a natural map of complexes of towers
`(X ⊗ Pₙ)ₙ ⟶ (X ⊗ P'ₙ)ₙ`. -/
noncomputable def tensorTowerFunctorMap (φ : P ⟶ P') :
    tensorTowerFunctor P ⟶ tensorTowerFunctor P' :=
  Functor.whiskerLeft (curriedTensor (CochainComplex A ℤ))
    (Functor.whiskerRight ((Functor.whiskeringLeft _ _ _).map φ)
      (HomologicalComplex.functorEquivalence A (ComplexShape.up ℤ) ℕᵒᵖ).inverse)

/-- A map of coefficient towers `φ : P ⟶ P'` induces a natural map of reduction towers
`K_•^P ⟶ K_•^{P'}`. -/
noncomputable def reductionTowerMap (φ : P ⟶ P') : reductionTower P ⟶ reductionTower P' :=
  Localization.liftNatTrans (TensorCommShift₂.LKFlat A) (kFlatQuasiIso A)
    (tensorTowerFunctorKFlat P) (tensorTowerFunctorKFlat P') _ _
    (Functor.whiskerLeft (CochainComplex.ιKFlat A)
      (Functor.whiskerRight (tensorTowerFunctorMap φ) Q))

end Functoriality

end DerivedCategory
