/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Connected

/-!
# The fibre of a constant sheaf at a point

For a point `Φ` of a site `(C, J)` and `M : A`, the fibre of the constant presheaf at `M` is
`M` (`CategoryTheory.GrothendieckTopology.Point.presheafFiberConstIso`): it is the colimit
of a constant functor over the connected category of elements of the fibre functor. When
`A` is concrete and `J.W` is the class of locally bijective morphisms, the fibre functor
inverts the sheafification maps, so the fibre of the constant sheaf at `M` is `M` as well
(`CategoryTheory.GrothendieckTopology.Point.sheafFiberConstantSheafIso`).

-/

@[expose] public section

universe w v u v' u'

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]

instance : IsConnected (Φ.fiber.Elements)ᵒᵖ :=
  IsFiltered.isConnected _

/-- The fibre of the constant presheaf at `M` is `M`: the colimit of a constant functor over
the connected category of elements of the fibre functor. -/
noncomputable def presheafFiberConstIso (M : A) :
    Φ.presheafFiber.obj ((Functor.const Cᵒᵖ).obj M) ≅ M :=
  colimit.isoColimitCocone ⟨_, isColimitConstCocone (Φ.fiber.Elements)ᵒᵖ M⟩

variable [HasWeakSheafify J A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [J.WEqualsLocallyBijective A] [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{w, w} (CategoryTheory.forget A)] [LocallySmall.{w} C]

/-- The fibre functor inverts the sheafification map of the constant presheaf. -/
instance isIso_presheafFiber_map_toSheafify_const (M : A) :
    IsIso (Φ.presheafFiber.map (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M))) :=
  Φ.W_isInvertedBy_presheafFiber' _ (J.W_toSheafify _)

/-- **The fibre of a constant sheaf at a point is its value**: `(M_C)_Φ ≅ M`. -/
noncomputable def sheafFiberConstantSheafIso (M : A) :
    Φ.sheafFiber.obj ((constantSheaf J A).obj M) ≅ M :=
  (asIso (Φ.presheafFiber.map (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)))).symm ≪≫
    Φ.presheafFiberConstIso M

end CategoryTheory.GrothendieckTopology.Point
