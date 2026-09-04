/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Skeletal

/-!
# The Picard group of a scheme and the Picard presheaf

For a scheme `Y` we define `AlgebraicGeometry.Scheme.Pic Y`, the set of isomorphism classes of
invertible sheaves of `𝒪_Y`-modules, as the invertible classes inside the skeleton of
`Y.Modules`, and its contravariant functoriality `AlgebraicGeometry.Scheme.Pic.pullback` given
by pulling back invertible modules.  For a morphism of schemes `f : X ⟶ S` this assembles into
the `Set`-valued Picard presheaf `T ↦ Pic (X ×[S] T)` on the category of schemes over `S`.

## Main definitions

- `AlgebraicGeometry.Scheme.Pic`: the Picard group of a scheme, as a set
  (blueprint `def:pcb-picard-group`).
- `AlgebraicGeometry.Scheme.picFunctor`: the Picard group as a functor `Schemeᵒᵖ ⥤ Type (u+1)`.
- `AlgebraicGeometry.picardPresheaf`: the Picard presheaf of `f : X ⟶ S`
  (blueprint `def:pc-picard-presheaf`).

## Implementation notes

Only the underlying *set* of the Picard group is defined; no group law is put on it.  The group
law is the tensor product of invertible modules, and Mathlib has the monoidal structure on
`PresheafOfModules` only, not on `SheafOfModules`; see the implementation notes of
`WeilConjectures/Mathlib/Algebra/Category/ModuleCat/Sheaf/LocallyFree.lean`.  A `Set`-valued
Picard presheaf is all that `AlgebraicGeometry.picardFunctor` needs.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- Invertibility of a sheaf of modules only depends on its isomorphism class, so it transfers
to the chosen representative of that class in the skeleton. -/
-- The universes of `IsInvertible.of_iso` have to be given explicitly: without them the
-- instance arguments of `of_iso` are elaborated before its category is known, and the
-- universe metavariables are defaulted to `0`.
lemma _root_.SheafOfModules.isInvertible_fromSkeleton_toSkeleton (M : Y.Modules)
    [M.IsInvertible] : ((fromSkeleton Y.Modules).obj (toSkeleton M)).IsInvertible :=
  SheafOfModules.IsInvertible.of_iso.{u, u, u} (fromSkeletonToSkeletonIso M).symm

variable (Y) in
/-- The Picard group of a scheme `Y`: the set of isomorphism classes of invertible sheaves
of `𝒪_Y`-modules, realized as the invertible classes inside the skeleton of `Y.Modules`.

This lives in `Type (u + 1)` rather than `Type u`: smallness of the Picard group is not
pursued here. -/
def Pic : Type (u + 1) :=
  { L : Skeleton Y.Modules // ((fromSkeleton Y.Modules).obj L).IsInvertible }

namespace Pic

/-- The isomorphism class in `Skeleton Y.Modules` underlying an element of `Y.Pic`. -/
def val (L : Y.Pic) : Skeleton Y.Modules :=
  Subtype.val L

lemma isInvertible (L : Y.Pic) : ((fromSkeleton Y.Modules).obj L.val).IsInvertible :=
  Subtype.property L

@[ext]
lemma ext {L L' : Y.Pic} (h : L.val = L'.val) : L = L' :=
  Subtype.ext h

/-- The class of an invertible sheaf of modules in the Picard group. -/
def mk (M : Y.Modules) [M.IsInvertible] : Y.Pic :=
  Subtype.mk (p := fun L ↦ ((fromSkeleton Y.Modules).obj L).IsInvertible) (toSkeleton M)
    (SheafOfModules.isInvertible_fromSkeleton_toSkeleton M)

@[simp]
lemma val_mk (M : Y.Modules) [M.IsInvertible] : (mk M).val = toSkeleton M :=
  rfl

lemma mk_eq_mk_iff (M N : Y.Modules) [M.IsInvertible] [N.IsInvertible] :
    mk M = mk N ↔ Nonempty (M ≅ N) := by
  rw [← toSkeleton_eq_toSkeleton_iff]
  exact ⟨fun h ↦ congrArg val h, fun h ↦ ext h⟩

/-- Pulling back invertible sheaves of modules along `g : X ⟶ Y` gives the map
`Pic Y → Pic X` underlying the functoriality of the Picard presheaf. -/
noncomputable def pullback (g : X ⟶ Y) (L : Y.Pic) : X.Pic :=
  Subtype.mk (p := fun L' ↦ ((fromSkeleton X.Modules).obj L').IsInvertible)
    ((Modules.pullback g).mapSkeleton.obj L.val) (by
      rw [Functor.mapSkeleton_obj]
      have := SheafOfModules.IsInvertible.pullback (g := g)
        (M := (fromSkeleton Y.Modules).obj L.val) L.isInvertible
      exact SheafOfModules.isInvertible_fromSkeleton_toSkeleton _)

@[simp]
lemma val_pullback (g : X ⟶ Y) (L : Y.Pic) :
    (pullback g L).val =
      toSkeleton ((Modules.pullback g).obj ((fromSkeleton Y.Modules).obj L.val)) :=
  rfl

@[simp]
lemma pullback_id (L : X.Pic) : pullback (𝟙 X) L = L := by
  refine ext ?_
  rw [val_pullback]
  conv_rhs => rw [← toSkeleton_fromSkeleton_obj L.val]
  exact congr_toSkeleton_of_iso ((Modules.pullbackId X).app _)

lemma pullback_comp {Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z) (L : Z.Pic) :
    pullback (g ≫ h) L = pullback g (pullback h L) := by
  refine ext ?_
  simp only [val_pullback]
  exact congr_toSkeleton_of_iso (((Modules.pullbackComp g h).app _).symm ≪≫
    (Modules.pullback g).mapIso (fromSkeletonToSkeletonIso _).symm)

end Pic

/-- The Picard group as a functor: a scheme is sent to its Picard group and a morphism of
schemes to the pullback map on Picard groups. -/
noncomputable def picFunctor : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj Y := Y.unop.Pic
  map g := TypeCat.ofHom (Pic.pullback g.unop)
  map_id _ := congrArg TypeCat.ofHom (funext Pic.pullback_id)
  map_comp _ _ := congrArg TypeCat.ofHom (funext fun L ↦ Pic.pullback_comp _ _ L)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

open Scheme

variable {X S : Scheme.{u}}

/-- The Picard presheaf of a morphism of schemes `f : X ⟶ S`: it sends a scheme `T` over `S`
to the Picard group of the fibre product `X_T = X ×[S] T`, and a morphism over `S` to the
corresponding pullback map on Picard groups.

The base change `T ↦ X ×[S] T` is `CategoryTheory.Over.pullback f`, followed by the forgetful
functor to schemes:

```text
  X ×[S] T' -------> X ×[S] T -------> X
      |                  |             |
      v                  v             f
      T' ---φ.left----> T ----T.hom--> S
```
-/
noncomputable def picardPresheaf (f : X ⟶ S) : (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  (Over.pullback f ⋙ Over.forget X).op ⋙ picFunctor

end AlgebraicGeometry
