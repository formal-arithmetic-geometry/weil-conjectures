/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.CategoryTheory.DerivedLimitRoosAbelianGroups
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Whiskering

/-!
# Milnor exact sequence for a derived inverse limit

Source: Stacks Project, More on Algebra, Tags 07KY and 08U5;
Derived Categories of Schemes, Tag 08D4, proof of (2)
(blueprint: lem-pc-derived-limit-milnor-sequence).

The maps are chosen simultaneously for all specified Roos triangles and are natural
for morphisms of these triangles. No functorial choice of a derived-limit object is assumed.
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

noncomputable section

attribute [local instance] roosTowerEnoughInjectives roosLimitAdditive


/-- The natural Milnor short exact sequence for every derived inverse limit of abelian groups.
Source: Stacks Project, Tags 07KY and 08U5; Tag 08D4, proof of (2)
(blueprint: lem-pc-derived-limit-milnor-sequence).

Proof, following the node:
1. Use the defining distinguished Roos triangle (`def-weil-derived-limit`). Exactness of
countable products in abelian groups (`lem-pc-abelian-groups-exact-products`) and part (2)
of `lem-weil-derived-limit-existence` identify the cohomology of the product with the
product of the cohomology groups, compatibly with every projection. Under this identification
cohomology sends the transition endomorphism to the transition endomorphism of the cohomology
system, since its projection is `pr n - pr (n + 1) ≫ f n`.
2. Apply `lem-sf-derived-homology-long-exact` to this triangle. The resulting five-term
segment starts with `1 - s` on the product in degree `i - 1` and ends with `1 - s` in
degree `i`. By `lem-pc-derived-limit-roos-abelian-groups`, their cokernel and kernel are
respectively the actual first right derived functor of inverse limit and inverse limit.
Factor the connecting map through that cokernel and the cohomology of `p` through that
kernel. Exactness gives the displayed short exact complex. The factorization of the latter
map is recorded by its equations after every limit projection. The natural Roos
identifications and natural long exact sequence give both commuting squares for every
morphism of specified triangles. This construction chooses the maps simultaneously.

`K` is the tower functor. The transition maps are recovered from its successor arrows.
The product instance supplies the product already present in the specified derived-limit
triangle, rather than a finiteness or boundedness hypothesis. All degrees are integers. -/
theorem milnor_shortExact [HasDerivedCategory.{v} AddCommGrpCat.{u}] (i : ℤ) :
    ∃ (a : ∀ (K : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
        [HasProduct (fun n : ℕ => K.obj (Opposite.op n))]
        (L : DerivedCategory AddCommGrpCat.{u})
        (_p : L ⟶ ∏ᶜ fun n : ℕ => K.obj (Opposite.op n))
        (_δ : (∏ᶜ fun n : ℕ => K.obj (Opposite.op n)) ⟶ L⟦(1 : ℤ)⟧),
        ((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived 1).obj (K ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1)) ⟶
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj L)
      (b : ∀ (K : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
        [HasProduct (fun n : ℕ => K.obj (Opposite.op n))]
        (L : DerivedCategory AddCommGrpCat.{u})
        (_p : L ⟶ ∏ᶜ fun n : ℕ => K.obj (Opposite.op n))
        (_δ : (∏ᶜ fun n : ℕ => K.obj (Opposite.op n)) ⟶ L⟦(1 : ℤ)⟧),
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj L ⟶ limit (K ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} i)),
      (∀ (K : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
        [HasProduct (fun n : ℕ => K.obj (Opposite.op n))]
        (L : DerivedCategory AddCommGrpCat.{u})
        (p : L ⟶ ∏ᶜ fun n : ℕ => K.obj (Opposite.op n))
        (δ : (∏ᶜ fun n : ℕ => K.obj (Opposite.op n)) ⟶ L⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle (fun n => K.map (homOfLE (Nat.le_succ n)).op) L p δ →
        (∃ hz : a K L p δ ≫ b K L p δ = 0,
          (ShortComplex.mk (a K L p δ) (b K L p δ) hz).ShortExact) ∧
        ∀ n : ℕ, b K L p δ ≫ limit.π (K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i)
          (Opposite.op n) =
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map (p ≫ Pi.π (fun n : ℕ => K.obj
            (Opposite.op n)) n)) ∧
      ∀ (K K' : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
        [HasProduct (fun n : ℕ => K.obj (Opposite.op n))]
        [HasProduct (fun n : ℕ => K'.obj (Opposite.op n))]
        (L L' : DerivedCategory AddCommGrpCat.{u})
        (p : L ⟶ ∏ᶜ fun n : ℕ => K.obj (Opposite.op n))
        (p' : L' ⟶ ∏ᶜ fun n : ℕ => K'.obj (Opposite.op n))
        (δ : (∏ᶜ fun n : ℕ => K.obj (Opposite.op n)) ⟶ L⟦(1 : ℤ)⟧)
        (δ' : (∏ᶜ fun n : ℕ => K'.obj (Opposite.op n)) ⟶ L'⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle (fun n => K.map (homOfLE (Nat.le_succ n)).op) L p δ →
        IsDerivedLimitTriangle (fun n => K'.map (homOfLE (Nat.le_succ n)).op) L' p' δ' →
        ∀ (φ : K ⟶ K') (g : L ⟶ L'),
          p ≫ Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n)) = g ≫ p' →
          δ ≫ (shiftFunctor _ (1 : ℤ)).map g =
            Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n)) ≫ δ' →
          ((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived 1).map
            (Functor.whiskerRight φ (DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1))) ≫ a
            K' L' p' δ' =
            a K L p δ ≫ (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map g ∧
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map g ≫ b K' L' p' δ' =
            b K L p δ ≫ limMap (Functor.whiskerRight φ (DerivedCategory.homologyFunctor
              AddCommGrpCat.{u} i)) := by
  sorry

end
end CategoryTheory
