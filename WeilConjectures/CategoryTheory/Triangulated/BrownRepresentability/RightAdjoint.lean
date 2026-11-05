/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.Basic
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure

/-!
# The Brown right adjoint of a coproduct-preserving triangulated functor

Let `C` be a pretriangulated category with `Hom`-types in `Type v`, with coproducts indexed by
`Type v` and a family of compact generators `S`
(`CategoryTheory.BrownRepresentability.CompactGenerators`), and let `F : C ⥤ D` be a triangulated
functor which preserves coproducts. Brown representability
(`CategoryTheory.Functor.isLeftAdjoint_of_compactGenerators`) shows that `F` has a right adjoint
`G`. We complete this to the abstract form of blueprint nodes `det-sf-existence-brown` and
`det-sf-existence-direct-sums`:

* `G` commutes with shifts compatibly with the adjunction and is triangulated, and any two right
  adjoints of `F` are isomorphic by a unique isomorphism compatible with the counits
  (`CategoryTheory.Functor.exists_rightAdjoint_of_compactGenerators`,
  `CategoryTheory.Adjunction.existsUnique_iso_comp_counit`);
* if moreover `F` sends the generators to compact objects, then `G` preserves coproducts
  (`CategoryTheory.Adjunction.preservesColimitsOfShape_discrete_of_compactGenerators`): the
  canonical map `∐ G(Nⱼ) ⟶ G(∐ Nⱼ)` induces bijections on `Hom(S i, -)` by compactness of
  `S i` and of `F(S i)`, hence is an isomorphism because the generators detect isomorphisms
  (`CategoryTheory.BrownRepresentability.CompactGenerators.isIso_of_bijective`).

We then specialize to localizing closures (`CategoryTheory.ObjectProperty.localizingClosure`).
A property `P` *compactly generates its localizing closure*
(`CategoryTheory.ObjectProperty.CompactlyGeneratesLocalizingClosure`) if it has a small set of
isomorphism representatives, its objects are compact in `Loc(P)` and detect zero objects of
`Loc(P)`. Given such `P₁`, `P₂` on pretriangulated categories `C₁`, `C₂` and a triangulated
functor `Φ : C₁ ⥤ C₂` mapping `Loc(P₁)` into `Loc(P₂)` and `P₁` into `P₂`, whose restriction to
`Loc(P₁)` preserves coproducts, the restricted functor
`Loc(P₁) ⥤ Loc(P₂)` (`CategoryTheory.ObjectProperty.localizingClosureLift`) has a triangulated,
coproduct-preserving right adjoint, unique up to unique isomorphism
(`CategoryTheory.ObjectProperty.exists_rightAdjoint_localizingClosureLift`). This is the formal
part of blueprint `sk-prop-sf-existence`.
-/

@[expose] public section

universe v u u' u₁ u₂

open CategoryTheory Limits Pretriangulated Category

namespace CategoryTheory

namespace BrownRepresentability

variable {C : Type u} [Category.{v} C]

variable [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

end BrownRepresentability

open BrownRepresentability

namespace Adjunction

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]

variable [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

end Adjunction

namespace Functor

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

end Functor

namespace ObjectProperty

section CompactlyGenerates

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)

variable {P}

end CompactlyGenerates

section Lift

variable {C₁ : Type u₁} [Category.{v} C₁] [Preadditive C₁] [HasZeroObject C₁] [HasShift C₁ ℤ]
  [∀ n : ℤ, (shiftFunctor C₁ n).Additive] [Pretriangulated C₁]
  {C₂ : Type u₂} [Category.{v} C₂] [Preadditive C₂] [HasZeroObject C₂] [HasShift C₂ ℤ]
  [∀ n : ℤ, (shiftFunctor C₂ n).Additive] [Pretriangulated C₂]
  (P₁ : ObjectProperty C₁) (P₂ : ObjectProperty C₂) (Φ : C₁ ⥤ C₂)
  (hΦ : ∀ X, P₁.localizingClosure X → P₂.localizingClosure (Φ.obj X))

variable [Φ.CommShift ℤ]

end Lift

end ObjectProperty

end CategoryTheory
