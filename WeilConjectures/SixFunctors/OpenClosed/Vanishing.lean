/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Complement

/-!
# `j^* i_*` and `i^* j_!` vanish for morphisms with disjoint ranges

Let `j : U ⟶ X` be an open immersion and let `i : Z ⟶ X` be an **arbitrary** morphism whose
range is disjoint from the range of `j`. This file proves that the extension by zero along `j`
and the pushforward along `i` see nothing of each other's side:

- `j^* i_* H` vanishes for every sheaf `H` on the small étale site of `Z`;
- `i^* j_! G` vanishes for every sheaf `G` on the small étale site of `U`.

In the intended application `i` is a closed immersion complementary to `j`, and these two
vanishings make the composite `j_! j^* F → F → i_* i^* F` zero. Neither statement needs `i` to
be a closed immersion, and the general form is what the rest of the argument uses.

## Main results

- `AlgebraicGeometry.Etale.isZero_upperStar_lowerStar_of_disjoint_range`: `j^* i_* H = 0`.
- `AlgebraicGeometry.Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range`:
  `i^* j_! G = 0`.

## Implementation details

These generalize the statements of
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Complement`, where `i` was an open
immersion too. Since `j_!` is a sheafification, `i^* j_! G` is treated through Hom-sets rather
than through sections.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

section Vanishing

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable {U Z X : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j]

open Etale

omit [HasSmallSiteSheafify A] in
/-- **`j^* i_* H` vanishes** when the ranges of `j` and `i` are disjoint. -/
lemma Etale.isZero_upperStar_lowerStar_of_disjoint_range
    (hji : Disjoint (Set.range j.base) (Set.range i.base))
    (H : Sheaf Z.smallEtaleTopology A) :
    IsZero ((j)^*[A].obj ((i)_*[A].obj H)) :=
  (Etale.isZero_openImmersionRestriction_lowerStar A i j hji.symm H).of_iso
    ((Etale.upperStarIsoOpenImmersionRestriction A j).app ((i)_*[A].obj H))

omit [HasSmallSiteSheafify A] in
/-- **`i^* j_! G` vanishes** when the ranges of `j` and `i` are disjoint. -/
lemma Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range
    (hji : Disjoint (Set.range j.base) (Set.range i.base))
    (G : Sheaf U.smallEtaleTopology A) :
    IsZero ((i)^*[A].obj ((j)_!open[A].obj G)) := by
  refine IsInitial.isZero (IsInitial.ofUnique (h := fun H ↦ ?_))
  have : Unique (G ⟶ (j)^*[A].obj ((i)_*[A].obj H)) :=
    have hz := Etale.isZero_upperStar_lowerStar_of_disjoint_range A j i hji H
    ⟨⟨hz.isTerminal.from G⟩, fun _ ↦ hz.isTerminal.hom_ext _ _⟩
  exact Equiv.unique
    (((Etale.upperStarLowerStarAdjunction A i).homEquiv ((j)_!open[A].obj G) H).trans
      ((Etale.openImmersionLowerShriekUpperStarAdjunction A j).homEquiv G ((i)_*[A].obj H)))

end Vanishing

end AlgebraicGeometry
