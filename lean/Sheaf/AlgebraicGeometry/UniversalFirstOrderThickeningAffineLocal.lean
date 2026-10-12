module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening

/-!
# Affine-local construction of universal first order thickenings

The affine-open construction in Stacks, More on Morphisms, Lemma 37.7.1 (Tag 04F3),
first produces a thickening with the lifting property for affine test schemes.
(blueprint: lem-weil-pbc-universal-first-order-thickening-affine-local)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The affine pieces of the square-zero construction and their gluing produce a
first-order thickening which has the universal lifting property for affine tests.
Source: Stacks, More on Morphisms, Lemma 37.7.1 (Tag 04F3), affine construction.
(blueprint: lem-weil-pbc-universal-first-order-thickening-affine-local)
Proof: choose an affine open cover, apply the affine square-zero construction, glue
the pieces using uniqueness on overlaps, and verify the lifting property whenever
both the test schemes are affine. -/
theorem FormallyUnramified.exists_affine_local_universalFirstOrderThickening
    {Z X : Scheme.{u}} (h : Z ⟶ X) [FormallyUnramified h] :
    ∃ (Z' : Scheme.{u}) (i : Z ⟶ Z') (h' : Z' ⟶ X),
      IsFirstOrderThickening i ∧ i ≫ h' = h ∧
        ∀ {T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
          (j : T ⟶ T') (b : T' ⟶ X) (a : T ⟶ Z),
          IsFirstOrderThickening j → j ≫ b = a ≫ h →
            ∃! a' : T' ⟶ Z', a' ≫ h' = b ∧ j ≫ a' = a ≫ i := by
  sorry

end AlgebraicGeometry
