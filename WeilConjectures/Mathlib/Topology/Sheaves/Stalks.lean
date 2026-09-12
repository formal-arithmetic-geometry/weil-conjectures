/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Stalks of a pushforward, and exactness properties of stalks

Let `f : X ⟶ Y` be a continuous map of topological spaces.

* `TopCat.Presheaf.pushforwardCompStalkFunctor` upgrades
  `TopCat.Presheaf.stalkPushforward` to a morphism of functors
  `f _* (-) ⋙ stalkFunctor C (f x) ⟶ stalkFunctor C x`, and
  `TopCat.Presheaf.pushforwardCompStalkFunctorIso` records that it is an isomorphism when
  `f` is inducing.
* `TopCat.Sheaf.isZero_stalk_pushforward_of_notMem_range`: if the range of `f` is closed,
  the stalk of `f _* F` at a point outside the range of `f` vanishes, for `F` a sheaf with
  values in a category with a zero object.

The last section records that taking stalks is left exact, because a stalk is a filtered
colimit, and that an epimorphism of sheaves is surjective on stalks.

* `TopCat.Presheaf.stalkFunctor_preservesFiniteLimits`
* `TopCat.Sheaf.surjective_stalkFunctor_map_of_epi`

-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite TopologicalSpace Topology

open scoped AlgebraicGeometry

noncomputable section

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] [HasColimits.{v} C] {X Y : TopCat.{v}}

variable (C) in
/-- `TopCat.Presheaf.stalkPushforward` as a morphism of functors: the stalk at `f x` of the
pushforward along `f` maps to the stalk at `x`. -/
def pushforwardCompStalkFunctor (f : X ⟶ Y) (x : X) :
    pushforward C f ⋙ stalkFunctor C (f x) ⟶ stalkFunctor C x where
  app F := F.stalkPushforward C f x
  naturality F G φ := by
    change (stalkFunctor C (f x)).map ((pushforward C f).map φ) ≫ G.stalkPushforward C f x =
      F.stalkPushforward C f x ≫ (stalkFunctor C x).map φ
    refine stalk_hom_ext _ fun U hU ↦ ?_
    simp

variable (C) in
/-- For an inducing map `f`, the stalk at `f x` of the pushforward along `f` of a presheaf is
its stalk at `x`, naturally in the presheaf. -/
def pushforwardCompStalkFunctorIso {f : X ⟶ Y} (hf : IsInducing f) (x : X) :
    pushforward C f ⋙ stalkFunctor C (f x) ≅ stalkFunctor C x :=
  have (F : X.Presheaf C) : IsIso ((pushforwardCompStalkFunctor C f x).app F) :=
    stalkPushforward.stalkPushforward_iso_of_isInducing C hf F x
  have : IsIso (pushforwardCompStalkFunctor C f x) := NatIso.isIso_of_isIso_app _
  asIso (pushforwardCompStalkFunctor C f x)

end TopCat.Presheaf

namespace TopCat.Sheaf

variable {C : Type u} [Category.{v} C] [HasColimits.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] {X Y : TopCat.{v}}

open Presheaf ZeroObject

/-- If the range of `f : X ⟶ Y` is closed, the stalk of the pushforward `f _* F` of a sheaf
`F` vanishes at every point outside the range of `f`. -/
lemma isZero_stalk_pushforward_of_notMem_range {f : X ⟶ Y} (hf : IsClosed (Set.range f))
    (F : X.Sheaf C) {y : Y} (hy : y ∉ Set.range f) :
    IsZero (((pushforward C f).obj F.presheaf).stalk y) := by
  let V : Opens Y := ⟨(Set.range f)ᶜ, hf.isOpen_compl⟩
  set G := (pushforward C f).obj F.presheaf with hG
  rw [IsZero.iff_id_eq_zero]
  refine stalk_hom_ext _ fun U hU ↦ ?_
  have hmem : y ∈ U ⊓ V := ⟨hU, hy⟩
  have hbot : (Opens.map f).obj (U ⊓ V) = ⊥ := by
    ext x
    exact ⟨fun hx ↦ absurd (Set.mem_range_self x) hx.2, fun hx ↦ hx.elim⟩
  have hzero : IsZero (G.obj (op (U ⊓ V))) :=
    IsZero.of_iso (isZero_zero C)
      ((F.isTerminalOfEqEmpty hbot).uniqueUpToIso (isZero_zero C).isTerminal)
  rw [Category.comp_id, comp_zero, ← germ_res G (homOfLE inf_le_left) y hmem,
    hzero.eq_zero_of_tgt (G.map (homOfLE (inf_le_left (a := U) (b := V))).op), zero_comp]

end TopCat.Sheaf

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
  [HasColimits.{v} C] [HasFiniteLimits C]
  [PreservesFiniteLimits (CategoryTheory.forget C)]
  [PreservesFilteredColimits (CategoryTheory.forget C)]
  [(CategoryTheory.forget C).ReflectsIsomorphisms] {X : TopCat.{v}}

/-- Taking stalks at a point is left exact: the stalk at `x` is the colimit over the filtered
category of open neighbourhoods of `x`, and filtered colimits commute with finite limits. -/
instance stalkFunctor_preservesFiniteLimits (x : X) :
    PreservesFiniteLimits (stalkFunctor C x) :=
  letI : PreservesFiniteLimits
      ((Functor.whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ C).obj (OpenNhds.inclusion x).op) :=
    inferInstance
  letI : PreservesFiniteLimits (colim : ((OpenNhds x)ᵒᵖ ⥤ C) ⥤ C) := inferInstance
  comp_preservesFiniteLimits _ _

end TopCat.Presheaf

namespace TopCat.Sheaf

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
  [HasColimits.{v} C] [PreservesFilteredColimits (CategoryTheory.forget C)] {X : TopCat.{v}}
  [Balanced (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)]
  [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget C)]
  [HasSheafify (Opens.grothendieckTopology X) C]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective C]
  [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization C]

/-- An epimorphism of sheaves is surjective on stalks: it is locally surjective, and a stalk
only remembers arbitrarily small neighbourhoods. -/
lemma surjective_stalkFunctor_map_of_epi {F G : TopCat.Sheaf C X} (φ : F ⟶ G) [Epi φ] (x : X) :
    Function.Surjective ((Presheaf.stalkFunctor C x).map φ.hom) :=
  (Presheaf.locally_surjective_iff_surjective_on_stalks _).1
    ((TopCat.Sheaf.isLocallySurjective_iff_epi φ).2 inferInstance) x

end TopCat.Sheaf
