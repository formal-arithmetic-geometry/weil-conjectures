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

section Augmentation

variable (A) in
set_option backward.isDefEq.respectTransparency false in
/-- The complex of constant towers attached to a complex `X` is the complex of towers
associated with the constant tower of complexes on `X`. -/
noncomputable def constMapHomologicalComplexIso :
    (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      Functor.const ℕᵒᵖ ⋙
        (HomologicalComplex.functorEquivalence A (ComplexShape.up ℤ) ℕᵒᵖ).inverse :=
  NatIso.ofComponents (fun X ↦ HomologicalComplex.Hom.isoOfComponents
    (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _)) (by intros; ext; simp; rfl))
    (by intros; ext; simp; rfl)

variable (A) in
/-- The right unitor `X ⟶ X ⊗ 𝟙`, as a map from the constant tower on `X` to the tower
`n ↦ X ⊗ 𝟙` of tensor products with the constant coefficient tower `𝟙`. -/
noncomputable def constToTensorConstUnit :
    (Functor.const ℕᵒᵖ : CochainComplex A ℤ ⥤ _) ⟶ curriedTensor (CochainComplex A ℤ) ⋙
      (Functor.whiskeringLeft _ _ _).obj ((Functor.const ℕᵒᵖ).obj (𝟙_ (CochainComplex A ℤ))) where
  app X :=
    { app _ := (ρ_ X).inv
      naturality _ _ _ := by
        change 𝟙 X ≫ (ρ_ X).inv = (ρ_ X).inv ≫ X ◁ 𝟙 (𝟙_ _)
        rw [Category.id_comp, MonoidalCategory.whiskerLeft_id, Category.comp_id] }
  naturality X Y f :=
    NatTrans.ext (funext fun _ ↦ MonoidalCategory.rightUnitor_inv_naturality f)

/-- The map of complexes of towers from the constant tower on `X` to `(X ⊗ Pₙ)ₙ` induced by an
augmentation `ε : 𝟙 ⟶ Pₙ` of the coefficient tower: `X ≅ X ⊗ 𝟙 ⟶ X ⊗ Pₙ`. -/
noncomputable def constToTensorTower {P : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (ε : (Functor.const ℕᵒᵖ).obj (𝟙_ (CochainComplex A ℤ)) ⟶ P) :
    (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      tensorTowerFunctor P :=
  (constMapHomologicalComplexIso A).hom ≫
    Functor.whiskerRight (constToTensorConstUnit A)
      (HomologicalComplex.functorEquivalence A (ComplexShape.up ℤ) ℕᵒᵖ).inverse ≫
    tensorTowerFunctorMap ε

/-- The constant tower functor restricted to K-flat complexes is computed termwise. -/
noncomputable def lKFlatCompTowerConstIso :
    TensorCommShift₂.LKFlat A ⋙ towerConst A ≅ CochainComplex.ιKFlat A ⋙
      (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q :=
  Functor.isoWhiskerLeft (CochainComplex.ιKFlat A)
    (Functor.isoWhiskerRight (quotientCompQhIso A) (towerConst A) ≪≫
      (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors)

/-- The map `const K ⟶ K_•` from the constant tower on `K` to the reduction tower of `K`
induced by an augmentation `ε : 𝟙 ⟶ Pₙ` of the coefficient tower: on a K-flat representative
`X` of `K`, it is `X ≅ X ⊗ 𝟙 ⟶ X ⊗ Pₙ`. -/
noncomputable def towerConstToReductionTower {P : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (ε : (Functor.const ℕᵒᵖ).obj (𝟙_ (CochainComplex A ℤ)) ⟶ P) :
    towerConst A ⟶ reductionTower P :=
  Localization.liftNatTrans (TensorCommShift₂.LKFlat A) (kFlatQuasiIso A)
    (TensorCommShift₂.LKFlat A ⋙ towerConst A) (tensorTowerFunctorKFlat P) _ _
    ((lKFlatCompTowerConstIso).hom ≫ Functor.whiskerLeft (CochainComplex.ιKFlat A)
      (Functor.whiskerRight (constToTensorTower ε) Q))

/-- **Blueprint `def-weil-pbc-completion-map`.** The completion map `comp_K : K ⟶ R lim K_•`
of an object `K` of `D(A)` into the derived limit of its reduction tower, induced by the
augmentation `ε : 𝟙 ⟶ Pₙ` of the coefficient tower. It is the map adjoint, under the derived
adjunction `const ⊣ R lim`, to the map `const K ⟶ K_•` given on K-flat representatives by
`X ≅ X ⊗ 𝟙 ⟶ X ⊗ Pₙ`. -/
noncomputable def completionMap {P : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (ε : (Functor.const ℕᵒᵖ).obj (𝟙_ (CochainComplex A ℤ)) ⟶ P) :
    𝟭 (DerivedCategory A) ⟶ reductionTower P ⋙ rlim A :=
  (towerConstAdjunction A).unit ≫ Functor.whiskerRight (towerConstToReductionTower ε) (rlim A)

end Augmentation

end DerivedCategory
