/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.CategoryTheory.DerivedLimitRoosAbelianGroups
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Whiskering

/-!
# Connecting-map factorization for the Milnor sequence

Source: Stacks Project, More on Algebra, Tags 07KW and 07KY.
(blueprint: lem-pc-milnor-boundary-factorization).
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
noncomputable section
attribute [local instance] roosTowerEnoughInjectives roosLimitAdditive

/-- Factor the connecting map of a Roos triangle through the first derived limit.
Source: Stacks Project, More on Algebra, Tag 07KY; Tag 07KW.
(blueprint: lem-pc-milnor-boundary-factorization).

Proof: preserve countable products under cohomology using Tag 07KC and identify
cohomology of the transition endomorphism componentwise with the Roos map.
The long exact cohomology sequence in degrees i-1 and i has a connecting map
from the product in degree i-1 to H^i(L). Its kernel is the image of the Roos map.
Descend through the cokernel and compose with the natural Roos isomorphism
R^1 lim H^{i-1}(K) to this cokernel (Tag 07KW). The descended arrow is mono
by exactness at the connecting map's source. Exactness at H^i(L) identifies
its image with the kernel of H^i(p). Both factorizations are unique since the
cokernel projection is epi. Naturality of the connecting map and of the Roos
isomorphism therefore gives the displayed naturality square. Choose zero maps
for triples which are not distinguished; for distinguished triples use these
unique factorizations. This chooses all maps simultaneously. -/
theorem milnor_boundary_factorization [HasDerivedCategory.{v} AddCommGrpCat.{u}]
    (i : ℤ) :
    ∃ (a : ∀ (K : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
        [HasProduct (fun n : ℕ => K.obj (Opposite.op n))]
        (L : DerivedCategory AddCommGrpCat.{u})
        (_p : L ⟶ ∏ᶜ fun n : ℕ => K.obj (Opposite.op n))
        (_δ : (∏ᶜ fun n : ℕ => K.obj (Opposite.op n)) ⟶ L⟦(1 : ℤ)⟧),
        ((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived 1).obj (K ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1)) ⟶
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj L),
      (∀ (K : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
        [HasProduct (fun n : ℕ => K.obj (Opposite.op n))]
        (L : DerivedCategory AddCommGrpCat.{u})
        (p : L ⟶ ∏ᶜ fun n : ℕ => K.obj (Opposite.op n))
        (δ : (∏ᶜ fun n : ℕ => K.obj (Opposite.op n)) ⟶ L⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle (fun n => K.map (homOfLE (Nat.le_succ n)).op) L p δ →
        Mono (a K L p δ) ∧
        ∃ hz : a K L p δ ≫
            ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map p ≫
              piComparison (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i)
                (fun n : ℕ => K.obj (Opposite.op n))) = 0,
          (ShortComplex.mk (a K L p δ)
            ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map p ≫
              piComparison (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i)
                (fun n : ℕ => K.obj (Opposite.op n))) hz).Exact) ∧
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
            a K L p δ ≫ (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map g := by
  sorry

end
end CategoryTheory
