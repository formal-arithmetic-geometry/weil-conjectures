/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
public import WeilConjectures.AlgebraicGeometry.TorsionAbelianBaseChange
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.BaseChange.EtaleDerived
public import WeilConjectures.SixFunctors.BaseChange.Square

/-!
# Blueprint statements

lemma-weil-pbc-target-locality.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Blueprint: lemma-weil-pbc-target-locality. -/
theorem derivedBaseChange_target_locality
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (I : Type w) (V Xi Yi' Xi' : I → Scheme.{u})
    (j : ∀ i, V i ⟶ Y) [∀ i, AlgebraicGeometry.Etale (j i)]
    (_hcover : ∀ y : Y, ∃ (i : I) (v : V i), (j i).base v = y)
    (fi : ∀ i, Xi i ⟶ V i) (jXi : ∀ i, Xi i ⟶ X)
    (_sqj : ∀ i, IsPullback (jXi i) (fi i) f (j i))
    (k : ∀ i, Yi' i ⟶ Y') (gi : ∀ i, Yi' i ⟶ V i)
    (_sqY : ∀ i, IsPullback (k i) (gi i) g (j i))
    (kXi : ∀ i, Xi' i ⟶ X') (fi' : ∀ i, Xi' i ⟶ Yi' i)
    (_sqk : ∀ i, IsPullback (kXi i) (fi' i) f' (k i))
    (gi' : ∀ i, Xi' i ⟶ Xi i)
    (_hcomponent : ∀ i, gi' i ≫ jXi i = kXi i ≫ g')
    (sqᵢ : ∀ i, CommSq (gi' i) (fi' i) (fi i) (gi i))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (∀ i, IsPullback (gi' i) (fi' i) (fi i) (gi i)) ∧
    (∀ i,
      IsIso ((upperStar AddCommGrpCat.{u + 1} (k i)).mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) ↔
      IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} (sqᵢ i)).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf (Xi i).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
          ((upperStar AddCommGrpCat.{u + 1} (jXi i)).obj F)))) ∧
    (IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) ↔
      ∀ i, IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} (sqᵢ i)).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf (Xi i).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
          ((upperStar AddCommGrpCat.{u + 1} (jXi i)).obj F)))) := by
  sorry

/-- Blueprint: lemma-weil-pbc-target-locality. -/
theorem hasTorsionAbelianBaseChange_of_etale_cover
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (I : Type w) (V Xi : I → Scheme.{u})
    (j : ∀ i, V i ⟶ Y) [∀ i, AlgebraicGeometry.Etale (j i)]
    (_hcover : ∀ y : Y, ∃ (i : I) (v : V i), (j i).base v = y)
    (fi : ∀ i, Xi i ⟶ V i) (jXi : ∀ i, Xi i ⟶ X)
    (_sqj : ∀ i, IsPullback (jXi i) (fi i) f (j i)) :
    (∀ i, IsProper (fi i)) ∧
      ((∀ i, HasTorsionAbelianBaseChange (fi i)) → HasTorsionAbelianBaseChange f) := by
  sorry

end AlgebraicGeometry.Etale
