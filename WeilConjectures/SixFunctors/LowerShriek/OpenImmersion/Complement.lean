/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleClopen
public import WeilConjectures.SixFunctors.LowerShriek.Comparison

/-!
# The extension by zero and the pushforward vanish off an open immersion

Let `j : U ⟶ X` and `k : W ⟶ X` be open immersions with **disjoint** ranges. This file proves
that both `k^* j_! F` and `k^* j_* F` are initial as sheaves on the small étale site of `W`,
and deduces that `k^*` of the comparison `j_! ⟶ j_*` is an isomorphism.

Together with the `j^*` half (`j_!` fully faithful for an open immersion), this discharges the
hypothesis `hkc` of
`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekToLowerStar_of_isIso_restriction`, and
it is the one place where the zero object of the abelian `A` is consumed — see the
counterexample recorded in the docstring of
`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekToLowerStar`.

## The argument

Everything rests on one geometric fact: for `T` étale over `W`, the fibre product `T ×_X U` is
**empty**, because the ranges of `j` and `k` are disjoint
(`AlgebraicGeometry.isEmpty_pullback_of_disjoint_range`). A sheaf has terminal sections over an
object with empty underlying scheme (`AlgebraicGeometry.Scheme.Etale.isTerminalSectionsOfIsEmpty`,
itself the sheaf condition for the empty covering), and with a zero object in `A` terminal means
zero. Hence:

- `k^* j_* F` has zero sections, since `(k^* j_* F)(T) = F(T ×_X U) = F(∅)`. A sheaf with zero
  sections is both initial and terminal.
- `k^* j_! F` is initial, and this is proved **without computing any of its sections** — `j_!`
  is a sheafification, which is exactly what makes the naive route hard. Instead, for every `H`,
  the two adjunctions give
  `Hom(k^* j_! F, H) ≃ Hom(j_! F, k_* H) ≃ Hom(F, j^* k_* H)`, and `j^* k_* H` has zero sections
  by the same computation with the roles of `j` and `k` exchanged. So the Hom-set is a singleton.

Both being initial, the comparison between them is *the* map out of an initial object, hence an
isomorphism.

## Main results

- `AlgebraicGeometry.isEmpty_pullback_of_disjoint_range`: the geometric input.
- `AlgebraicGeometry.Etale.isZero_openImmersionRestriction_lowerStar` and
  `AlgebraicGeometry.Etale.isInitial_openImmersionRestriction_openImmersionLowerShriek`: the two
  vanishing statements.
- `AlgebraicGeometry.Etale.isIso_openImmersionRestriction_openImmersionLowerShriekToLowerStar`:
  `k^*` of the comparison is an isomorphism, for disjoint `j` and `k`.
- `AlgebraicGeometry.Etale.isIso_clopenComplement_openImmersionLowerShriekToLowerStar`: the same
  statement in the shape the reduction lemma of
  `WeilConjectures.SixFunctors.LowerShriek.Comparison` consumes, with `k` the inclusion of the
  complement of a clopen `j`. This is `hkc`.
- `AlgebraicGeometry.Etale`
  `.isIso_openImmersionLowerShriekToLowerStar_of_isIso_openImmersionRestriction`: the resulting
  one-hypothesis reduction of the clopen case, which is what remains of it.

Also proved here, and generic enough to be upstreamable as they stand:
`CategoryTheory.Sheaf.isTerminalOfIsTerminalObj`, `CategoryTheory.Sheaf.isZero_of_isZero_obj`
and `CategoryTheory.Sheaf.isInitialOfIsZeroObj` — a sheaf whose sections are all terminal (resp.
zero) is terminal (resp. zero, hence initial), for an arbitrary site and coefficient category.
-/

@[expose] public section

universe v₁ u₁ v' u' u

open CategoryTheory Category Limits Opposite

/-! ### Sheaves whose sections vanish -/

namespace CategoryTheory.Sheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A]

/-- A sheaf whose sections are all terminal is terminal. -/
noncomputable def isTerminalOfIsTerminalObj (F : Sheaf J A) (h : ∀ U, IsTerminal (F.obj.obj U)) :
    IsTerminal F :=
  IsTerminal.isTerminalOfObj (sheafToPresheaf J A) _ (Functor.isTerminal h)

/-- A sheaf whose sections are all zero objects is a zero object. Morphisms of sheaves are
morphisms of the underlying presheaves, so this is `CategoryTheory.Functor.isZero` transported
along `CategoryTheory.Sheaf.homEquiv`. -/
lemma isZero_of_isZero_obj (F : Sheaf J A) (h : ∀ U, IsZero (F.obj.obj U)) : IsZero F := by
  have h1 : IsZero F.obj := Functor.isZero _ h
  refine ⟨fun G => ?_, fun G => ?_⟩
  · obtain ⟨u⟩ := h1.unique_to G.obj
    exact ⟨Equiv.unique Sheaf.homEquiv⟩
  · obtain ⟨u⟩ := h1.unique_from G.obj
    exact ⟨Equiv.unique Sheaf.homEquiv⟩

/-- A sheaf whose sections are all zero objects is initial. -/
noncomputable def isInitialOfIsZeroObj (F : Sheaf J A) (h : ∀ U, IsZero (F.obj.obj U)) :
    IsInitial F :=
  (isZero_of_isZero_obj F h).isInitial

end CategoryTheory.Sheaf

namespace AlgebraicGeometry

/-! ### Emptiness of a fibre product over disjoint opens -/

section Geometry

variable {U X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- If `j` is an open immersion whose range is disjoint from the range of `f`, the fibre
product `V ×_X U` is empty. -/
lemma isEmpty_pullback_of_disjoint_range {V : Scheme.{u}} (f : V ⟶ X) (j : U ⟶ X)
    [IsOpenImmersion j] (h : Set.range f.base ∩ Set.range j.base = ∅) :
    IsEmpty ↥(Limits.pullback f j) := by
  have hr : Set.range (Limits.pullback.fst f j).base = ∅ := by
    rw [IsOpenImmersion.range_pullbackFst]
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have hmem : f.base x ∈ Set.range f.base ∩ Set.range j.base := ⟨⟨x, rfl⟩, hx⟩
    rw [h] at hmem
    exact hmem
  exact Set.range_eq_empty_iff.mp hr

end Geometry

/-! ### The sections of `k^* j_*` and of `j^* k_*` -/

section Disjoint

variable (A : Type u') [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]
variable {U W X : Scheme.{u}} (j : U ⟶ X) (k : W ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]

set_option backward.isDefEq.respectTransparency false in
/-- For `T` étale over `W`, the fibre product `T ×_X U` is empty when the ranges of `j` and `k`
are disjoint: `T` maps into the range of `k`, which misses the range of `j`. -/
lemma Scheme.Etale.isEmpty_left_pullback_map
    (hjk : Set.range j.base ∩ Set.range k.base = ∅) (T : W.Etale) :
    IsEmpty ((MorphismProperty.Over.pullback @Etale ⊤ j).obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : @Etale _ _ k)).obj T)).left := by
  refine isEmpty_pullback_of_disjoint_range (T.hom ≫ k) j (Set.eq_empty_of_subset_empty ?_)
  rintro x ⟨⟨t, rfl⟩, hx⟩
  rw [← hjk]
  exact ⟨hx, ⟨T.hom.base t, rfl⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The sections of `k^* j_* F` over `T : W.Etale` are `F(T ×_X U) = F(∅)`, hence terminal. -/
noncomputable def Etale.isTerminalSections_openImmersionRestriction_lowerStar
    (hjk : Set.range j.base ∩ Set.range k.base = ∅)
    (F : Sheaf U.smallEtaleTopology A) (T : W.Etale) :
    IsTerminal ((((Etale.openImmersionRestriction A k).obj
      ((Etale.lowerStar A j).obj F))).obj.obj (op T)) :=
  letI := Scheme.Etale.isEmpty_left_pullback_map j k hjk T
  Scheme.Etale.isTerminalSectionsOfIsEmpty F
    ((MorphismProperty.Over.pullback @Etale ⊤ j).obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : @Etale _ _ k)).obj T))

set_option backward.isDefEq.respectTransparency false in
omit [IsGrothendieckAbelian.{u} A] in
/-- **`k^* j_* F` vanishes.** All its sections are terminal, hence zero. -/
lemma Etale.isZero_openImmersionRestriction_lowerStar
    (hjk : Set.range j.base ∩ Set.range k.base = ∅) (F : Sheaf U.smallEtaleTopology A) :
    IsZero ((Etale.openImmersionRestriction A k).obj ((Etale.lowerStar A j).obj F)) := by
  refine Sheaf.isZero_of_isZero_obj _ ?_
  rintro ⟨T⟩
  exact IsZero.of_iso (isZero_zero A)
    ((Etale.isTerminalSections_openImmersionRestriction_lowerStar A j k hjk F T).uniqueUpToIso
      HasZeroObject.zeroIsTerminal)

set_option backward.isDefEq.respectTransparency false in
/-- **`k^* j_! F` is initial**, proved through Hom-sets rather than through sections: the two
adjunctions turn `Hom(k^* j_! F, H)` into `Hom(F, j^* k_* H)`, and `j^* k_* H` vanishes by
`AlgebraicGeometry.Etale.isZero_openImmersionRestriction_lowerStar` with the roles of `j` and
`k` exchanged. -/
noncomputable def Etale.isInitial_openImmersionRestriction_openImmersionLowerShriek
    (hjk : Set.range j.base ∩ Set.range k.base = ∅) (F : Sheaf U.smallEtaleTopology A) :
    IsInitial ((Etale.openImmersionRestriction A k).obj
      ((Etale.openImmersionLowerShriek A j).obj F)) := by
  refine IsInitial.ofUnique (h := fun H => ?_)
  haveI : Unique (F ⟶ (Etale.openImmersionRestriction A j).obj ((Etale.lowerStar A k).obj H)) := by
    have hz := Etale.isZero_openImmersionRestriction_lowerStar A k j
      (by rw [Set.inter_comm]; exact hjk) H
    exact ⟨⟨hz.isTerminal.from F⟩, fun a => hz.isTerminal.hom_ext _ _⟩
  exact Equiv.unique
    (((Etale.openImmersionRestrictionLowerStarAdjunction A k).homEquiv _ H).trans
      ((Etale.openImmersionLowerShriekAdjunction A j).homEquiv F _))

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison `j_! ⟶ j_*` restricted to a disjoint open is an isomorphism.** Both sides
are initial, and a morphism out of an initial object is unique, so it agrees with the canonical
isomorphism between the two. -/
lemma Etale.isIso_openImmersionRestriction_openImmersionLowerShriekToLowerStar
    (hjk : Set.range j.base ∩ Set.range k.base = ∅) (F : Sheaf U.smallEtaleTopology A) :
    IsIso ((Etale.openImmersionRestriction A k).map
      ((Etale.openImmersionLowerShriekToLowerStar A j).app F)) := by
  have hS := Etale.isInitial_openImmersionRestriction_openImmersionLowerShriek A j k hjk F
  have hT := (Etale.isZero_openImmersionRestriction_lowerStar A j k hjk F).isInitial
  have key : (Etale.openImmersionRestriction A k).map
      ((Etale.openImmersionLowerShriekToLowerStar A j).app F) = (hS.uniqueUpToIso hT).hom :=
    hS.hom_ext _ _
  rw [key]
  infer_instance

end Disjoint

/-! ### The complement of a clopen immersion -/

section Clopen

variable {U X : Scheme.{u}}

/-- An open immersion with clopen range and the inclusion of the complementary open subscheme
have **disjoint** ranges. `AlgebraicGeometry.Scheme.Hom.range_union_range_clopenComplement_ι`
is the other half; conservativity only needs that one, but the vanishing statements of this
file need this one. -/
lemma Scheme.Hom.range_inter_range_clopenComplement_ι (j : U ⟶ X) [IsOpenImmersion j]
    (hj : IsClopen (Set.range j.base)) :
    Set.range j.base ∩ Set.range (j.clopenComplement hj).ι.base = ∅ := by
  rw [Scheme.Opens.range_ι]
  exact Set.inter_compl_self _

variable (A : Type u') [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]
variable (j : U ⟶ X) [IsOpenImmersion j]

set_option backward.isDefEq.respectTransparency false in
/-- **The hypothesis `hkc` of
`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekToLowerStar_of_isIso_restriction`.**
For an open immersion `j` with clopen range and `k` the inclusion of the complementary open
subscheme, `k^*` of the comparison `j_! ⟶ j_*` is an isomorphism. -/
lemma Etale.isIso_clopenComplement_openImmersionLowerShriekToLowerStar
    (hj : IsClopen (Set.range j)) (F : Sheaf U.smallEtaleTopology A) :
    IsIso ((Etale.openImmersionRestriction A (Scheme.Hom.clopenComplement j hj).ι).map
      ((Etale.openImmersionLowerShriekToLowerStar A j).app F)) :=
  Etale.isIso_openImmersionRestriction_openImmersionLowerShriekToLowerStar A j _
    (Scheme.Hom.range_inter_range_clopenComplement_ι j hj) F

set_option backward.isDefEq.respectTransparency false in
/-- **The clopen case of `j_! ≅ j_*` now depends on the restriction along `j` alone.** With the
complement half discharged, the only remaining input to
`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekToLowerStar` is that `j^*` of the
comparison is an isomorphism, which — since `j^* j_* F ≅ F` is the inverted counit used to build
the comparison — says exactly that `j_!` is fully faithful for an open immersion. That statement
carries no clopen hypothesis and is not yet in this repository. -/
lemma Etale.isIso_openImmersionLowerShriekToLowerStar_of_isIso_openImmersionRestriction
    (hj : IsClopen (Set.range j))
    (hjc : ∀ F, IsIso ((Etale.openImmersionRestriction A j).map
      ((Etale.openImmersionLowerShriekToLowerStar A j).app F))) :
    IsIso (Etale.openImmersionLowerShriekToLowerStar A j) :=
  Etale.isIso_openImmersionLowerShriekToLowerStar_of_isIso_restriction A j hj hjc
    (Etale.isIso_clopenComplement_openImmersionLowerShriekToLowerStar A j hj)

end Clopen

end AlgebraicGeometry
