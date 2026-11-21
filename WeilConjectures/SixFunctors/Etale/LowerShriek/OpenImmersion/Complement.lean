/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison

/-!
# The extension by zero and the pushforward vanish off an open immersion

Let `j : U ⟶ X` and `k : W ⟶ X` be open immersions with **disjoint** ranges. This file proves
that both `k^* j_! F` and `k^* j_* F` are initial as sheaves on the small étale site of `W`,
and deduces that `k^*` of the comparison `j_! ⟶ j_*` is an isomorphism.

Together with the `j^*` half (`j_!` fully faithful for an open immersion, proved in
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful`), this is the
sheaf-theoretic input to the comparison `j_! ⟶ j_*` being an isomorphism for an open
immersion with closed range.

## Main results

- `AlgebraicGeometry.Etale.isZero_openImmersionRestriction_lowerStar` and
  `AlgebraicGeometry.Etale.isInitial_openImmersionRestriction_openImmersionLowerShriek`: the two
  vanishing statements.
- `AlgebraicGeometry.Etale.isIso_openImmersionRestriction_openImmersionLowerShriekToLowerStar`:
  `k^*` of the comparison is an isomorphism, for disjoint `j` and `k`.

## Implementation details

The zero object of the abelian `A` is genuinely needed: for `A = Type` and `k` with nonempty
source, `k^* j_* F` has singleton sections `F(∅)` while `k^* j_! F` is empty. The vanishing of
`k^* j_! F` is proved through Hom-sets, `Hom(k^* j_! F, H) ≃ Hom(F, j^* k_* H)`, without
computing sections of the sheafification `j_!`. The general sheaf-theoretic inputs live in
`WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf` and are shared with the pro-étale
counterpart `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement`.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

/-! ### The sections of `k^* j_*` and of `j^* k_*` -/

section Disjoint

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable {U W X : Scheme.{u}} (j : U ⟶ X) (k : W ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]

open Etale

omit [IsOpenImmersion j] in
set_option backward.isDefEq.respectTransparency false in
/-- For `T` étale over `W`, the fibre product `T ×_X U` is empty when the ranges of `j` and `k`
are disjoint. Only `k` is assumed to be an open immersion; `j` may be an arbitrary morphism. -/
lemma Scheme.Etale.isEmpty_left_pullback_map
    (hjk : Disjoint (Set.range j.base) (Set.range k.base)) (T : W.Etale) :
    IsEmpty ((MorphismProperty.Over.pullback @Etale ⊤ j).obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : @Etale _ _ k)).obj T)).left := by
  refine Scheme.isEmpty_pullback (T.hom ≫ k) j (Set.disjoint_left.mpr ?_)
  rintro x ⟨t, rfl⟩ hx
  exact Set.disjoint_left.mp hjk hx ⟨T.hom.base t, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The sections of `k^* j_* F` over `T : W.Etale` are `F(T ×_X U) = F(∅)`, hence terminal. -/
noncomputable def Etale.isTerminalSections_openImmersionRestriction_lowerStar
    (hjk : Disjoint (Set.range j.base) (Set.range k.base))
    (F : Sheaf U.smallEtaleTopology A) (T : W.Etale) :
    IsTerminal ((((Etale.openImmersionRestriction A k).obj
      ((j)_*[A].obj F))).obj.obj (op T)) :=
  letI := Scheme.Etale.isEmpty_left_pullback_map j k hjk T
  Scheme.Etale.isTerminalSectionsOfIsEmpty F
    ((MorphismProperty.Over.pullback @Etale ⊤ j).obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : @Etale _ _ k)).obj T))

set_option backward.isDefEq.respectTransparency false in
omit [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] [IsOpenImmersion j] in
/-- **`k^* j_* F` vanishes**, for `j` an arbitrary morphism whose range is disjoint from that of
the open immersion `k`. -/
lemma Etale.isZero_openImmersionRestriction_lowerStar
    (hjk : Disjoint (Set.range j.base) (Set.range k.base)) (F : Sheaf U.smallEtaleTopology A) :
    IsZero ((Etale.openImmersionRestriction A k).obj ((j)_*[A].obj F)) := by
  refine Sheaf.isZero_of_isZero_obj _ ?_
  rintro ⟨T⟩
  exact IsZero.of_iso (isZero_zero A)
    ((Etale.isTerminalSections_openImmersionRestriction_lowerStar A j k hjk F T).uniqueUpToIso
      HasZeroObject.zeroIsTerminal)

set_option backward.isDefEq.respectTransparency false in
/-- **`k^* j_! F` is initial**, for open immersions `j` and `k` with disjoint ranges. -/
noncomputable def Etale.isInitial_openImmersionRestriction_openImmersionLowerShriek
    (hjk : Disjoint (Set.range j.base) (Set.range k.base)) (F : Sheaf U.smallEtaleTopology A) :
    IsInitial ((Etale.openImmersionRestriction A k).obj ((j)_!open[A].obj F)) := by
  refine IsInitial.ofUnique (h := fun H ↦ ?_)
  have : Unique (F ⟶ (Etale.openImmersionRestriction A j).obj ((k)_*[A].obj H)) := by
    have hz := Etale.isZero_openImmersionRestriction_lowerStar A k j hjk.symm H
    exact ⟨⟨hz.isTerminal.from F⟩, fun _ ↦ hz.isTerminal.hom_ext _ _⟩
  exact Equiv.unique
    (((Etale.openImmersionRestrictionLowerStarAdjunction A k).homEquiv _ H).trans
      ((Etale.openImmersionLowerShriekAdjunction A j).homEquiv F _))

set_option backward.isDefEq.respectTransparency false in
omit [HasSmallSiteSheafify A] in
/-- **The comparison `j_! ⟶ j_*` restricted to a disjoint open is an isomorphism.** -/
lemma Etale.isIso_openImmersionRestriction_openImmersionLowerShriekToLowerStar
    (hjk : Disjoint (Set.range j.base) (Set.range k.base)) (F : Sheaf U.smallEtaleTopology A) :
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


end AlgebraicGeometry
