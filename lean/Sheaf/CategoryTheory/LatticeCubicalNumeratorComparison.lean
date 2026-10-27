/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.CategoryTheory.LatticeCubicalMultiplicationData

/-! # Cubical multiplication and unit numerators

Source: direct-images paragraph (3), lattice expansion, steps 2--3 and unit in step 6
(blueprint: lem-sfb-lattice-cubical-numerator-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace Profinite.DiscreteLattice.CubicalMultiplication

variable (R : CategoryTheory.CondensedBar.Ring.{u}) (r : ℕ)
    (J : CubicalEvaluation.DiscreteComparison R r)
    (C : CubicalEvaluation.CubicalModel R r)
    (K : KoszulModel R.toMon r) (B : DerivedCup.Algebra R.toMon r)

variable (P : FlatTwisted.Pairing K B)

/-- The finite coefficient calculation compares the two chain-map numerators and the unit.
Source: cubical roof proof steps 2--3 and the unit part of step 6
(blueprint: lem-sfb-lattice-cubical-numerator-comparison).

Proof: use the normalized evaluation on each pair of Koszul subset inclusions and each
free cell inclusion. By the pairing coordinates the first numerator is zero unless
A and C are disjoint with union I. In the remaining case it is
c_(p+q) epsilon(A,C) T^v(x_A) T^(v+u_A)(y_C), using multiplicativity and commuting
actions. Expand the diagonal for the second numerator. The same conditions leave one
partition; the signed middle interchange contributes (-1)^(pq), and the two evaluations
give c_p and c_q. The identity (p+q)(p+q+1)/2=p(p+1)/2+q(q+1)/2+pq equates the signs.
Tensor coproduct universal properties and the Koszul biproduct coordinates prove equality
of the degree-zero maps. The target is zero in other degrees. For the unit only Koszul
degree zero survives: positive cells map to zero and a vertex maps to T^v(1)=1.
Thus unit evaluation is exactly augmentation followed by the original algebra unit.
The same coefficient computation proves the displayed first-numerator equation. -/
theorem normalized_roof_numerators [IsCommMonObj B.X]
    (F : Roof (koszul R r K B) (lattice R r J C) (algebra R r B))
    (hF : Normalized R r J C K B F) :
    F.f (star R r K B P) = F.comparison ≫ F.g (mul R r B) ∧
    (unit R r K B P ⊗ₘ 𝟙 (lattice R r J C)) ≫ F.evaluation =
      (λ_ (lattice R r J C)).hom ≫ F.augmentation ≫ eta R r B ∧
    (∀ (p q : ℕ) (A : Subsets r (p : ℤ)) (A' : Subsets r (q : ℤ))
        (v : Fin r → ℤ) (I : Subsets r ((p : ℤ) + q)),
      supported R r J C K B p q A A' v I ≫
        ((F.f (star R r K B P)).f 0).hom ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B.X).hom.hom =
          value R r B p q A A' v I) := by sorry

end Profinite.DiscreteLattice.CubicalMultiplication
