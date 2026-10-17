/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
public import WeilConjectures.CategoryTheory.StageSystem.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.ScalarExtensionComp

/-!
# The stage system of the rational coefficient categories

Let `ℓ` be a prime and `Y` a scheme. For a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`
(`PadicAlgCl.FiniteIntermediateField ℓ`) let `C_E(Y) = D_comp(Y_ét, E)` be the rationalized
category of derived complete `𝒪_E`-complexes (`DerivedCategoryDerivedCompleteRational`). For
`E ⊆ F` the scalar extensions `T_{F/E} = - ⊗_E F : C_E(Y) ⥤ C_F(Y)`
(`AlgebraicGeometry.Etale.derivedCompleteRationalScalarExtension`) and their composition
isomorphisms `T_{G/F} ∘ T_{F/E} ≅ T_{G/E}`
(`AlgebraicGeometry.Etale.derivedCompleteRationalScalarExtensionCompIso`) form a stage system
in the sense of `CategoryTheory.StageSystem`: the composition isomorphisms satisfy the cocycle
condition (`AlgebraicGeometry.Etale.derivedCompleteRationalScalarExtensionCompIso_cocycle`).

This is the concrete instance of blueprint `def-weil-pbc-finite-stage-pair-category` at the
coefficient categories `D_comp(Y_ét, E)`, with the associators of blueprint
`prop-weil-pbc-scalar-extension`; its pair category is the colimit category
`D_comp(Y_ét, ℚ̄_ℓ)` of blueprint `def-weil-pbc-qbar-category`.

## Main definitions

- `AlgebraicGeometry.Etale.rationalScalarExtensionStage`: the scalar extension `T_{F/E}`.
- `AlgebraicGeometry.Etale.rationalStageSystem`: the stage system `E ↦ D_comp(Y_ét, E)`.
- `AlgebraicGeometry.Etale.DerivedCategoryDerivedCompleteQbar`: its pair category.
-/

@[expose] public section

universe u

open CategoryTheory PadicAlgCl

attribute [local instance] AlgebraicGeometry.Scheme.Etale.essentiallySmall

namespace AlgebraicGeometry.Etale

variable (l : ℕ) [Fact l.Prime]

/-- The algebra structure of a finite subextension `F` of `ℚ̄_ℓ` over a smaller one `E`, given
by the inclusion. -/
noncomputable abbrev finiteIntermediateFieldAlgebra {E F : FiniteIntermediateField l}
    (h : E ≤ F) : Algebra E.1 F.1 :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

lemma isScalarTower_finiteIntermediateField {E F : FiniteIntermediateField l} (h : E ≤ F) :
    letI := finiteIntermediateFieldAlgebra l h
    IsScalarTower E.1 F.1 (PadicAlgCl l) :=
  letI := finiteIntermediateFieldAlgebra l h
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

instance (E : FiniteIntermediateField l) : Small.{u + 1} E.1 := small_lift _

variable (Y : Scheme.{u})

/-- The rational coefficient category `C_E(Y) = D_comp(Y_ét, E)` at the finite stage `E`. -/
abbrev RationalStage (E : FiniteIntermediateField l) : Type _ :=
  DerivedCategoryDerivedCompleteRational.{0, u} Y.smallEtaleTopology l E.1

/-- Blueprint `prop-weil-pbc-scalar-extension`: the scalar extension
`T_{F/E} = - ⊗_E F : D_comp(Y_ét, E) ⥤ D_comp(Y_ét, F)` for finite subextensions `E ⊆ F` of
`ℚ̄_ℓ`. -/
noncomputable def rationalScalarExtensionStage {E F : FiniteIntermediateField l} (h : E ≤ F) :
    RationalStage l Y E ⥤ RationalStage l Y F :=
  letI := finiteIntermediateFieldAlgebra l h
  haveI := isScalarTower_finiteIntermediateField l h
  derivedCompleteRationalScalarExtension l E.1 F.1

/-- Blueprint `prop-weil-pbc-scalar-extension`: the associator
`T_{G/F} ∘ T_{F/E} ≅ T_{G/E}` of the scalar extensions. -/
noncomputable def rationalScalarExtensionStageCompIso {E F G : FiniteIntermediateField l}
    (h : E ≤ F) (h' : F ≤ G) :
    rationalScalarExtensionStage l Y h ⋙ rationalScalarExtensionStage l Y h' ≅
      rationalScalarExtensionStage l Y (h.trans h') :=
  letI := finiteIntermediateFieldAlgebra l h
  letI := finiteIntermediateFieldAlgebra l h'
  letI := finiteIntermediateFieldAlgebra l (h.trans h')
  haveI := isScalarTower_finiteIntermediateField l h
  haveI := isScalarTower_finiteIntermediateField l h'
  haveI := isScalarTower_finiteIntermediateField l (h.trans h')
  derivedCompleteRationalScalarExtensionCompIso l E.1 F.1 G.1 Y

/-- Blueprint `prop-weil-pbc-scalar-extension` (associator equation): the associators of the
scalar extensions satisfy the cocycle condition. -/
lemma rationalScalarExtensionStageCompIso_cocycle {E F G H : FiniteIntermediateField l}
    (h₁ : E ≤ F) (h₂ : F ≤ G) (h₃ : G ≤ H) (X : RationalStage l Y E) :
    (rationalScalarExtensionStage l Y h₃).map
        ((rationalScalarExtensionStageCompIso l Y h₁ h₂).hom.app X) ≫
      (rationalScalarExtensionStageCompIso l Y (h₁.trans h₂) h₃).hom.app X =
    (rationalScalarExtensionStageCompIso l Y h₂ h₃).hom.app
        ((rationalScalarExtensionStage l Y h₁).obj X) ≫
      (rationalScalarExtensionStageCompIso l Y h₁ (h₂.trans h₃)).hom.app X := by
  letI := finiteIntermediateFieldAlgebra l h₁
  letI := finiteIntermediateFieldAlgebra l h₂
  letI := finiteIntermediateFieldAlgebra l h₃
  letI := finiteIntermediateFieldAlgebra l (h₁.trans h₂)
  letI := finiteIntermediateFieldAlgebra l (h₂.trans h₃)
  letI := finiteIntermediateFieldAlgebra l ((h₁.trans h₂).trans h₃)
  haveI := isScalarTower_finiteIntermediateField l h₁
  haveI := isScalarTower_finiteIntermediateField l h₂
  haveI := isScalarTower_finiteIntermediateField l h₃
  haveI := isScalarTower_finiteIntermediateField l (h₁.trans h₂)
  haveI := isScalarTower_finiteIntermediateField l (h₂.trans h₃)
  haveI := isScalarTower_finiteIntermediateField l ((h₁.trans h₂).trans h₃)
  exact derivedCompleteRationalScalarExtensionCompIso_cocycle l E.1 F.1 G.1 H.1 Y X

/-- Blueprint `def-weil-pbc-finite-stage-pair-category`: the stage system of the rational
coefficient categories `E ↦ D_comp(Y_ét, E)` over the finite subextensions `E ⊆ ℚ̄_ℓ`, with the
scalar extensions `T_{F/E}` as transition functors and their composition isomorphisms as
associators. -/
noncomputable def rationalStageSystem : StageSystem (RationalStage l Y) where
  T h := rationalScalarExtensionStage l Y h
  assoc h h' := rationalScalarExtensionStageCompIso l Y h h'
  cocycle h₁ h₂ h₃ X := rationalScalarExtensionStageCompIso_cocycle l Y h₁ h₂ h₃ X

/-- Blueprint `def-weil-pbc-qbar-category`: the `ℚ̄_ℓ`-coefficient category
`D_comp(Y_ét, ℚ̄_ℓ)`, the pair category of the stage system of the rational coefficient
categories: an object is a pair `(E, K)` with `K ∈ D_comp(Y_ét, E)`, a morphism
`(E, K) ⟶ (F, L)` a class of morphisms `T_{M/E} K ⟶ T_{M/F} L` at a common finite stage `M`. -/
abbrev DerivedCategoryDerivedCompleteQbar : Type _ :=
  (rationalStageSystem l Y).PairCategory

end AlgebraicGeometry.Etale
