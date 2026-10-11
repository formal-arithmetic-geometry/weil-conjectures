/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-!

# The external Hom map

For two complexes `E₁, L₁` on `Z₁` and `E₂, L₂` on `Z₂` over a base `B`, the *external Hom map*
of `def-sf-kv-maps` (iii) (`sk-def-sf-kv-maps`)

`β : RHom(E₁, L₁) ⊠ RHom(E₂, L₂) ⟶ RHom(E₁ ⊠ E₂, L₁ ⊠ L₂)`

is the tensor–Hom transpose of the two evaluations, with the tensor symmetry (the Koszul
braiding of the derived category) and its signs:

`(E₁ ⊠ E₂) ⊗ᴸ (RHom(E₁, L₁) ⊠ RHom(E₂, L₂)) ≅ (E₁ ⊗ᴸ RHom(E₁, L₁)) ⊠ (E₂ ⊗ᴸ RHom(E₂, L₂))
  ⟶ L₁ ⊠ L₂`.

## Main definitions

- `DerivedCategory.koszulBraidedCategory`: the Koszul braiding of a derived category, as a
  named (non-instance) definition.
- `CategoryTheory.MonoidalClosed.externalIhomMap`: the external internal-hom map
  `F₁(E₁ ⟶[D₁] L₁) ⊗ F₂(E₂ ⟶[D₂] L₂) ⟶ (F₁ E₁ ⊗ F₂ E₂ ⟶[C] F₁ L₁ ⊗ F₂ L₂)` for lax monoidal
  functors `Fᵢ : Dᵢ ⥤ C` into a braided closed monoidal category.
- `AlgebraicGeometry.Etale.externalHomMap` (`def-sf-kv-maps` (iii)): the map `β`.

-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace DerivedCategory

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

local instance : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

/-- The Koszul braiding of the derived category of a braided monoidal closed Grothendieck abelian
category with functorial flat resolutions, `CategoryTheory.DerivedMonoidal.braidedCategory`, as a
named definition (its existence is `DerivedCategory.nonempty_braidedCategory`). -/
noncomputable def koszulBraidedCategory [HasDerivedCategory.{w} C] [MonoidalCategory C]
    [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] :
    BraidedCategory (DerivedCategory C) :=
  DerivedMonoidal.braidedCategory Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

end DerivedCategory

namespace CategoryTheory.MonoidalClosed

universe v₀ v₁ v₂ u₀ u₁ u₂

variable {C : Type u₀} {D₁ : Type u₁} {D₂ : Type u₂} [Category.{v₀} C] [Category.{v₁} D₁]
  [Category.{v₂} D₂] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
  [MonoidalCategory D₁] [MonoidalClosed D₁] [MonoidalCategory D₂] [MonoidalClosed D₂]
  (F₁ : D₁ ⥤ C) (F₂ : D₂ ⥤ C) [F₁.LaxMonoidal] [F₂.LaxMonoidal]

/-- The external internal-hom map
`F₁(E₁ ⟶[D₁] L₁) ⊗ F₂(E₂ ⟶[D₂] L₂) ⟶ (F₁ E₁ ⊗ F₂ E₂ ⟶[C] F₁ L₁ ⊗ F₂ L₂)`: the transpose of
`(F₁ E₁ ⊗ F₂ E₂) ⊗ (F₁ H₁ ⊗ F₂ H₂) ⟶ (F₁ E₁ ⊗ F₁ H₁) ⊗ (F₂ E₂ ⊗ F₂ H₂) ⟶ F₁ L₁ ⊗ F₂ L₂`, the
middle-four interchange `tensorμ` followed by the images of the two evaluations
(`Hᵢ = Eᵢ ⟶ Lᵢ`). -/
noncomputable def externalIhomMap (E₁ L₁ : D₁) (E₂ L₂ : D₂) :
    F₁.obj ((ihom E₁).obj L₁) ⊗ F₂.obj ((ihom E₂).obj L₂) ⟶
      (ihom (F₁.obj E₁ ⊗ F₂.obj E₂)).obj (F₁.obj L₁ ⊗ F₂.obj L₂) :=
  curry (tensorμ _ _ _ _ ≫
    ((Functor.LaxMonoidal.μ F₁ _ _ ≫ F₁.map ((ihom.ev E₁).app L₁)) ⊗ₘ
      (Functor.LaxMonoidal.μ F₂ _ _ ≫ F₂.map ((ihom.ev E₂).app L₂))))

end CategoryTheory.MonoidalClosed

universe u' u

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

namespace Etale

/-- Blueprint `def-sf-kv-maps` (iii), `sk-def-sf-kv-maps` (iii): the external Hom map

`β : RHom(E₁, L₁) ⊠ RHom(E₂, L₂) ⟶ RHom(E₁ ⊠ E₂, L₁ ⊠ L₂)`

for `Eᵢ, Lᵢ ∈ D(Zᵢ_ét)` and `cᵢ : Zᵢ ⟶ B`, the external products being taken over `B`. It is the
tensor–Hom transpose of the two evaluations
(`CategoryTheory.MonoidalClosed.externalIhomMap` for the monoidal functors `Lp₁^*`, `Lp₂^*`),
with the tensor symmetry the Koszul braiding of `D((Z₁ ×_B Z₂)_ét)`
(`DerivedCategory.koszulBraidedCategory`). -/
noncomputable def externalHomMap {B Z₁ Z₂ : Scheme.{u}} (c₁ : Z₁ ⟶ B) (c₂ : Z₂ ⟶ B)
    (E₁ L₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology A))
    (E₂ L₂ : _root_.DerivedCategory (Sheaf Z₂.smallEtaleTopology A)) :
    externalProduct A c₁ c₂ ((RHom(Z₁)[A].obj (op E₁)).obj L₁) ((RHom(Z₂)[A].obj (op E₂)).obj L₂) ⟶
      (RHom(pullback c₁ c₂)[A].obj (op (externalProduct A c₁ c₂ E₁ E₂))).obj
        (externalProduct A c₁ c₂ L₁ L₂) :=
  letI := _root_.DerivedCategory.koszulBraidedCategory (Sheaf (pullback c₁ c₂).smallEtaleTopology A)
  letI := leftDerivedUpperStarMonoidal A (pullback.fst c₁ c₂)
  letI := leftDerivedUpperStarMonoidal A (pullback.snd c₁ c₂)
  MonoidalClosed.externalIhomMap (L((pullback.fst c₁ c₂)^*[A])) (L((pullback.snd c₁ c₂)^*[A]))
    E₁ L₁ E₂ L₂

end Etale

end AlgebraicGeometry
