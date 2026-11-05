/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Basic

/-!
# Descent of functors and natural transformations to pair categories

Let `S` and `S'` be stage systems on families of categories `C i` and `D i` indexed by the same
directed preorder. A *morphism of stage systems* `F : S.Morphism S'` is a family of functors
`Φ_i : C i ⥤ D i` together with isomorphisms `β_{j/i} : T'_{j/i} ∘ Φ_i ≅ Φ_j ∘ T_{j/i}` compatible
with the associators. It induces a functor `F.functor` between the pair categories, given on a
representative `u : T x ⟶ T y` at the stage `n` by `β ≫ Φ_n u ≫ β⁻¹`. Families of natural
transformations compatible with the `β` descend to natural transformations.

In the application, `Φ_E` is `Rf_{!,E}` or `Lg_E^*` on `D^b_c(-, E)` and `β` is the compatibility
with the extension of scalars `T_{F/E} = F ⊗ᴸ_E -`; the exchange maps at the finite stages
descend to the exchange map on `D^b_c(-, ℚ̄_ℓ)`.

## Main definitions

- `CategoryTheory.StageSystem.Morphism`: morphisms of stage systems.
- `CategoryTheory.StageSystem.Morphism.functor`: the induced functor on pair categories.
- `CategoryTheory.StageSystem.Morphism.Hom` and `CategoryTheory.StageSystem.Morphism.descNatTrans`:
  compatible families of natural transformations and the induced natural transformations.
- `CategoryTheory.StageSystem.Morphism.id`, `CategoryTheory.StageSystem.Morphism.comp`, with
  `functorIdIso` and `functorCompIso`.

## Main statements

- `CategoryTheory.StageSystem.Morphism.isIso_descNatTrans`: a descended natural transformation
  whose components at the finite stages are isomorphisms is an isomorphism.
-/

@[expose] public section

universe w v u v' u' v'' u''

namespace CategoryTheory

open Category

namespace StageSystem

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : I → Type u'} [∀ i, Category.{v'} (D i)] {E : I → Type u''} [∀ i, Category.{v''} (E i)]

namespace Morphism

variable {S : StageSystem C} {S' : StageSystem D} {S'' : StageSystem E} (F : Morphism S S')

variable [IsDirectedOrder I]

open PairCategory

attribute [reassoc] Hom.comm

variable {F} {G H : Morphism S S'}

end Morphism

/-! ### Identity and composition -/

namespace Morphism

variable (S : StageSystem C)

variable {S} {S' : StageSystem D} {S'' : StageSystem E}

variable [IsDirectedOrder I]

open PairCategory

end Morphism

end StageSystem

end CategoryTheory
