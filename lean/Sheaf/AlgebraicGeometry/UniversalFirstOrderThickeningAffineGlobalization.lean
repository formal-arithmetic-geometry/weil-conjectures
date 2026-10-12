module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening

/-!
# Globalization of affine lifting for universal first order thickenings

The affine-test lifting property globalizes by affine covers and morphism gluing.
(blueprint: lem-weil-pbc-universal-first-order-thickening-globalization)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Affine-test universality of a first-order thickening implies universality for all
test schemes. Source: Stacks, More on Morphisms, Lemma 37.7.1 (Tag 04F3), gluing step.
(blueprint: lem-weil-pbc-universal-first-order-thickening-globalization)
Proof: cover the test target by affine opens, apply affine-test uniqueness and existence,
then glue the local lifts; equality on overlaps follows from affine-test uniqueness. -/
theorem isUniversalFirstOrderThickening_of_affine_local
    {Z X Z' : Scheme.{u}} (h : Z ⟶ X) (i : Z ⟶ Z') (h' : Z' ⟶ X)
    (hi : IsFirstOrderThickening i) (hcomp : i ≫ h' = h)
    (haffine : ∀ {T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
      (j : T ⟶ T') (b : T' ⟶ X) (a : T ⟶ Z),
      IsFirstOrderThickening j → j ≫ b = a ≫ h →
        ∃! a' : T' ⟶ Z', a' ≫ h' = b ∧ j ≫ a' = a ≫ i) :
    IsUniversalFirstOrderThickening h i h' := by
  sorry

end AlgebraicGeometry
