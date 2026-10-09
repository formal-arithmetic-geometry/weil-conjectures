/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Tactic.DeriveFintype

/-!
# Coequalizers as quotients by a monoid action

Let `f g : Z ⟶ P` be two morphisms in a category with binary coproducts. The coproduct
`P ⨿ Z` carries an action of the three-element monoid `{1, l, r}` with `x * y = y` for
`x, y ≠ 1` (`CategoryTheory.Limits.ParallelPairMonoid`): `l` acts by `𝟙 P ⨿ f` and `r` by
`𝟙 P ⨿ g`, both mapping `Z` into `P`. A quotient of `P ⨿ Z` by this action is the same as a
coequalizer of `f` and `g`. Hence a category with binary coproducts and quotients by finite
monoid actions has coequalizers
(`CategoryTheory.Limits.hasCoequalizers_of_hasColimitsOfShape_singleObj`).

This is used to construct coequalizers of finite étale schemes (blueprint
`lem-fet-finite-limits`).
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Limits

/-- The monoid `{1, l, r}` with `x * y = y` for `x, y ≠ 1`: the identity adjoined to the
right-zero semigroup on two elements. -/
inductive ParallelPairMonoid : Type w
  /-- The identity. -/
  | one
  /-- The element acting through the first morphism. -/
  | left
  /-- The element acting through the second morphism. -/
  | right
  deriving DecidableEq, Fintype

namespace ParallelPairMonoid

instance : Monoid ParallelPairMonoid.{w} where
  one := one
  mul x y := match x, y with
    | one, y => y
    | x, one => x
    | _, y => y
  mul_assoc x y z := by cases x <;> cases y <;> cases z <;> rfl
  one_mul x := by cases x <;> rfl
  mul_one x := by cases x <;> rfl

instance : Finite ParallelPairMonoid.{w} := inferInstance

end ParallelPairMonoid

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] {Z P : C} (f g : Z ⟶ P)

/-- The endomorphism of `P ⨿ Z` through which an element of `ParallelPairMonoid` acts. -/
noncomputable def parallelPairMonoidAct : ParallelPairMonoid.{w} → (P ⨿ Z ⟶ P ⨿ Z)
  | .one => 𝟙 _
  | .left => coprod.desc coprod.inl (f ≫ coprod.inl)
  | .right => coprod.desc coprod.inl (g ≫ coprod.inl)

lemma inl_parallelPairMonoidAct (m : ParallelPairMonoid.{w}) :
    coprod.inl ≫ parallelPairMonoidAct f g m = coprod.inl := by
  cases m <;> simp [parallelPairMonoidAct]

lemma parallelPairMonoidAct_comp (m n : ParallelPairMonoid.{w}) :
    parallelPairMonoidAct f g m ≫ parallelPairMonoidAct f g n =
      parallelPairMonoidAct f g (n * m) := by
  cases m <;> cases n <;> apply coprod.hom_ext <;> simp [parallelPairMonoidAct]

/-- The action of `ParallelPairMonoid` on `P ⨿ Z` whose quotient is the coequalizer of `f` and
`g`. -/
@[simps]
noncomputable def parallelPairMonoidFunctor : SingleObj ParallelPairMonoid.{w} ⥤ C where
  obj _ := P ⨿ Z
  map m := parallelPairMonoidAct f g m
  map_id _ := rfl
  map_comp m n := (parallelPairMonoidAct_comp f g m n).symm

/-- A quotient of `P ⨿ Z` by the action of `ParallelPairMonoid` gives a cofork of `f` and
`g`. -/
noncomputable def coforkOfCocone (c : Cocone (parallelPairMonoidFunctor.{w} f g)) : Cofork f g :=
  Cofork.ofπ (coprod.inl ≫ c.ι.app (SingleObj.star _)) (by
    have hl := c.w (j := SingleObj.star _) (j' := SingleObj.star _) ParallelPairMonoid.left
    have hr := c.w (j := SingleObj.star _) (j' := SingleObj.star _) ParallelPairMonoid.right
    simp only [parallelPairMonoidFunctor_map, parallelPairMonoidAct] at hl hr
    have hl' := coprod.inr ≫= hl
    have hr' := coprod.inr ≫= hr
    simp only [coprod.inr_desc_assoc, Category.assoc] at hl' hr'
    rw [hl', hr'])

/-- A cofork of `f` and `g` gives a cocone over the action of `ParallelPairMonoid`. -/
noncomputable def coconeOfCofork (t : Cofork f g) :
    Cocone (parallelPairMonoidFunctor.{w} f g) where
  pt := t.pt
  ι :=
    { app _ := coprod.desc t.π (f ≫ t.π)
      naturality _ _ m := by
        cases m
        · exact (Category.id_comp _).trans (Category.comp_id _).symm
        all_goals apply coprod.hom_ext <;> simp [parallelPairMonoidAct, t.condition] }

/-- The cofork obtained from a quotient of `P ⨿ Z` by the action of `ParallelPairMonoid` is a
coequalizer. -/
noncomputable def isColimitCoforkOfCocone {c : Cocone (parallelPairMonoidFunctor.{w} f g)}
    (hc : IsColimit c) : IsColimit (coforkOfCocone f g c) :=
  Cofork.IsColimit.mk _ (fun t ↦ hc.desc (coconeOfCofork f g t))
    (fun t ↦ by
      simp [coforkOfCocone, coconeOfCofork])
    (fun t m hm ↦ by
      refine hc.hom_ext fun j ↦ ?_
      obtain rfl : j = SingleObj.star _ := rfl
      rw [hc.fac]
      have hl := c.w (j := SingleObj.star _) (j' := SingleObj.star _) ParallelPairMonoid.left
      simp only [parallelPairMonoidFunctor_map, parallelPairMonoidAct] at hl
      have hl' := coprod.inr ≫= hl
      simp only [coprod.inr_desc_assoc, Category.assoc] at hl'
      apply coprod.hom_ext
      · simpa [coforkOfCocone, coconeOfCofork] using hm
      · simp only [coprod.inr_desc, coconeOfCofork]
        rw [← reassoc_of% hl', ← hm]
        simp [coforkOfCocone])

/-- A category with binary coproducts and quotients by finite monoid actions has
coequalizers: the coequalizer of `f g : Z ⟶ P` is the quotient of `P ⨿ Z` by the action of
`ParallelPairMonoid`. -/
lemma hasCoequalizers_of_hasColimitsOfShape_singleObj
    [HasColimitsOfShape (SingleObj ParallelPairMonoid.{w}) C] : HasCoequalizers C :=
  @hasCoequalizers_of_hasColimit_parallelPair _ _ fun {_ _ f g} ↦
    ⟨⟨_, isColimitCoforkOfCocone f g
      (colimit.isColimit (parallelPairMonoidFunctor.{w} f g))⟩⟩

end CategoryTheory.Limits
