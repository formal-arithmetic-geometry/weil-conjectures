/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.CategoryTheory.NatIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.IsIso
public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Etale

/-!

# Restriction along a jointly surjective family of open immersions is conservative

Let `g i : W i ⟶ X` be a family of open immersions whose ranges cover `X`. This file proves
that a morphism `φ` of `A`-valued sheaves on the small étale site of `X` is an isomorphism
as soon as all its restrictions `g i ^* φ` are
(`AlgebraicGeometry.Etale.isIso_of_isIso_openImmersionRestriction`). No hypothesis on the
coefficient category `A` is needed beyond what is required to state the restriction functors:
in particular the argument does not go through stalks.

## The argument

Given `V : X.Etale`, the base changes `V ×_X W i` cover `V` in the small étale topology
(`AlgebraicGeometry.Scheme.Etale.ofArrows_baseChange_mem_smallEtaleTopology`), and every
object of the sieve they generate maps to some `V ×_X W i`, hence has a structure morphism
factoring through some `g i`. On such an object the sections of `φ` agree, up to the
isomorphism `AlgebraicGeometry.Scheme.Etale.LiftIndex.isoComp`, with the sections of
`g i ^* φ`, which is an isomorphism by hypothesis. So `φ` is invertible on a covering sieve
of every object, and `CategoryTheory.Sheaf.isIso_of_isIso_app_of_mem` applies.

Note that no *disjointness* of the ranges is used, only that they cover `X`.

## Main results

- `AlgebraicGeometry.Etale.isIso_of_isIso_openImmersionRestriction`, stated for the
  restriction `AlgebraicGeometry.Etale.openImmersionRestriction`.
- `AlgebraicGeometry.Etale.isIso_of_isIso_upperStar`, the same statement for the pullback
  `AlgebraicGeometry.Etale.upperStar`, which agrees with the restriction by
  `AlgebraicGeometry.Etale.upperStarIsoOpenImmersionRestriction`.
- `AlgebraicGeometry.Etale.isIso_of_isIso_openImmersionRestriction_pair` and
  `AlgebraicGeometry.Etale.isIso_of_isIso_openImmersionRestriction_of_isClopen`: the
  two-element case, and its specialization to an open immersion with clopen range together
  with the inclusion `AlgebraicGeometry.Scheme.Hom.clopenComplement` of the complementary
  open subscheme.

## Intended use

For a *clopen* immersion `j : U ⟶ X` with complementary open immersion `k : W ⟶ X`, the
family `{j, k}` is jointly surjective, so proving that the comparison
`AlgebraicGeometry.Etale.openImmersionLowerShriekToLowerStar` is an isomorphism reduces to
proving that `j^*` and `k^*` of it are. That is the remaining content of
`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekToLowerStar`; see the module
docstring of `WeilConjectures.SixFunctors.LowerShriek.Comparison`.

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

namespace Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (V : X.Etale)

set_option backward.isDefEq.respectTransparency false in
/-- The base change `V ×_X U` lifts through `j`, via the second projection. -/
noncomputable def liftIndexBaseChange : LiftIndex j (baseChange j V) :=
  ⟨pullback.snd V.hom j, pullback.condition.symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- Any étale `X`-scheme mapping to the base change `V ×_X U` lifts through `j`. This is
what makes the covering of `V` by the base changes useful: not only the members of the
covering family, but every object of the sieve they generate, lies over `U`. -/
noncomputable def liftIndexOfHomBaseChange {T : X.Etale} (a : T ⟶ baseChange j V) : LiftIndex j T :=
  ⟨a.left ≫ pullback.snd V.hom j, by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact MorphismProperty.Over.w a⟩

end Scheme.Etale

section Conservative

variable (A : Type u') [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]
variable {X : Scheme.{u}} {ι : Type*} {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X)
  [∀ i, IsOpenImmersion (g i)]

set_option backward.isDefEq.respectTransparency false in
omit [Abelian A] [IsGrothendieckAbelian.{u} A] in
/-- **Restriction along a jointly surjective family of open immersions is conservative.**
A morphism of `A`-valued étale sheaves on `X` whose restrictions along a family of open
immersions `g i : W i ⟶ X` covering `X` are isomorphisms is itself an isomorphism. -/
theorem Etale.isIso_of_isIso_openImmersionRestriction
    (hg : ⋃ i, Set.range (g i).base = Set.univ)
    {G G' : Sheaf X.smallEtaleTopology A} (φ : G ⟶ G')
    (h : ∀ i, IsIso ((Etale.openImmersionRestriction A (g i)).map φ)) :
    IsIso φ := by
  refine Sheaf.isIso_of_isIso_app_of_mem _ φ fun V => ⟨_,
    Scheme.Etale.ofArrows_baseChange_mem_smallEtaleTopology V g hg, ?_⟩
  rintro T u ⟨Y, a, b, ⟨i⟩, rfl⟩
  -- Every object of the sieve maps to some `V ×_X W i`, hence lifts through `g i`.
  have hrest : ∀ b : (W i).Etale, IsIso (φ.hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : @Etale _ _ (g i))).obj b))) := by
    intro b
    haveI := h i
    haveI : IsIso (((Etale.openImmersionRestriction A (g i)).map φ).hom) :=
      inferInstanceAs (IsIso ((sheafToPresheaf _ A).map
        ((Etale.openImmersionRestriction A (g i)).map φ)))
    exact inferInstanceAs
      (IsIso ((((Etale.openImmersionRestriction A (g i)).map φ).hom).app (op b)))
  let α : Scheme.Etale.LiftIndex (g i) T := Scheme.Etale.liftIndexOfHomBaseChange (g i) V a
  haveI := hrest α.toEtale
  exact NatTrans.isIso_app_of_iso φ.hom α.isoComp.op.symm

set_option backward.isDefEq.respectTransparency false in
/-- The version of `AlgebraicGeometry.Etale.isIso_of_isIso_openImmersionRestriction` phrased
with the pullback `AlgebraicGeometry.Etale.upperStar` instead of the restriction; the two
agree for an open immersion by
`AlgebraicGeometry.Etale.upperStarIsoOpenImmersionRestriction`. -/
theorem Etale.isIso_of_isIso_upperStar (hg : ⋃ i, Set.range (g i).base = Set.univ)
    {G G' : Sheaf X.smallEtaleTopology A} (φ : G ⟶ G')
    (h : ∀ i, IsIso ((Etale.upperStar A (g i)).map φ)) :
    IsIso φ := by
  refine Etale.isIso_of_isIso_openImmersionRestriction A g hg φ fun i => ?_
  haveI := h i
  have key : (Etale.openImmersionRestriction A (g i)).map φ =
      inv ((Etale.upperStarIsoOpenImmersionRestriction A (g i)).hom.app G) ≫
        (Etale.upperStar A (g i)).map φ ≫
          (Etale.upperStarIsoOpenImmersionRestriction A (g i)).hom.app G' := by
    rw [IsIso.eq_inv_comp]
    exact ((Etale.upperStarIsoOpenImmersionRestriction A (g i)).hom.naturality φ).symm
  rw [key]
  infer_instance

end Conservative

section Pair

variable (A : Type u') [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]
variable {U W X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
omit [Abelian A] [IsGrothendieckAbelian.{u} A] in
/-- The two-element case of
`AlgebraicGeometry.Etale.isIso_of_isIso_openImmersionRestriction`: a morphism of étale
sheaves on `X` whose restrictions along two open immersions covering `X` are isomorphisms is
an isomorphism. -/
theorem Etale.isIso_of_isIso_openImmersionRestriction_pair
    (j : U ⟶ X) (k : W ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hjk : Set.range j.base ∪ Set.range k.base = Set.univ)
    {G G' : Sheaf X.smallEtaleTopology A} (φ : G ⟶ G')
    (hj : IsIso ((Etale.openImmersionRestriction A j).map φ))
    (hk : IsIso ((Etale.openImmersionRestriction A k).map φ)) :
    IsIso φ := by
  let Z : Bool → Scheme.{u} := fun b => bif b then U else W
  let f : ∀ b, Z b ⟶ X := fun b => Bool.rec (motive := fun b => Z b ⟶ X) k j b
  haveI : ∀ b, IsOpenImmersion (f b) := by rintro (_ | _) <;> assumption
  refine Etale.isIso_of_isIso_openImmersionRestriction A f ?_ φ ?_
  · have hu : (⋃ b, Set.range (f b).base) = Set.range k.base ∪ Set.range j.base := by
      ext x
      simp [Bool.exists_bool, f, Z]
    rw [hu, Set.union_comm]
    exact hjk
  · rintro (_ | _)
    exacts [hk, hj]

/-- The open complement of the range of an open immersion with clopen range. -/
def Scheme.Hom.clopenComplement (j : U ⟶ X) [IsOpenImmersion j]
    (hj : IsClopen (Set.range j.base)) : X.Opens :=
  ⟨(Set.range j.base)ᶜ, hj.isClosed.isOpen_compl⟩

/-- An open immersion with clopen range and the inclusion of the complementary open
subscheme are jointly surjective. -/
lemma Scheme.Hom.range_union_range_clopenComplement_ι (j : U ⟶ X) [IsOpenImmersion j]
    (hj : IsClopen (Set.range j.base)) :
    Set.range j.base ∪ Set.range (j.clopenComplement hj).ι.base = Set.univ := by
  rw [Scheme.Opens.range_ι]
  exact Set.union_compl_self _

set_option backward.isDefEq.respectTransparency false in
omit [Abelian A] [IsGrothendieckAbelian.{u} A] in
/-- For an open immersion `j` with **clopen** range, a morphism of étale sheaves on `X` is an
isomorphism as soon as its restrictions along `j` and along the inclusion of the
complementary open subscheme are. This is the form in which the conservativity is meant to
be used for `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekToLowerStar`: on the
complement both the extension by zero and the pushforward vanish, so only the restriction
along `j` itself carries content. -/
theorem Etale.isIso_of_isIso_openImmersionRestriction_of_isClopen
    (j : U ⟶ X) [IsOpenImmersion j] (hj : IsClopen (Set.range j.base))
    {G G' : Sheaf X.smallEtaleTopology A} (φ : G ⟶ G')
    (hjφ : IsIso ((Etale.openImmersionRestriction A j).map φ))
    (hkφ : IsIso ((Etale.openImmersionRestriction A (j.clopenComplement hj).ι).map φ)) :
    IsIso φ :=
  Etale.isIso_of_isIso_openImmersionRestriction_pair A j _
    (j.range_union_range_clopenComplement_ι hj) φ hjφ hkφ

end Pair

end AlgebraicGeometry
