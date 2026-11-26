/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Flasque
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Mathlib.Topology.Sheaves.Flasque
import WeilConjectures.AlgebraicGeometry.InjectiveRestrictionSurjective

/-!
# Flasque sheaves are acyclic

A flasque abelian sheaf on a topological space has vanishing cohomology in positive degrees.

## Implementation details

The proof applies `IsFlasque.subsingleton_H` and identifies `H' F q ⊤` with `H F q`: the free
abelian sheaf on the representable presheaf of the top open is the sheafification of the
constant presheaf `ULift ℤ`, and `Ext.precompAddEquiv` transports the subsingleton instance.

## References

* [Stacks Project, Tag 09SY](https://stacks.math.columbia.edu/tag/09SY)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf

/-- A flasque abelian sheaf on a topological space `X` has vanishing cohomology
`H^q(X, F) = Sheaf.H' F q ⊤` in every positive degree `q`. -/
theorem IsFlasque.subsingleton_H'_top {X : TopCat.{u}}
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Sheaf.IsFlasque F] (q : ℕ) (hq : 0 < q) :
    Subsingleton (CategoryTheory.Sheaf.H' F q ⊤) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  have : Subsingleton (CategoryTheory.Sheaf.H.{u} F (n + 1)) :=
    IsFlasque.subsingleton_H n F
  let e : yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free ≅
      (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
    NatIso.ofComponents (fun U ↦ by
      letI : Unique (U.unop ⟶ (⊤ : Opens X)) :=
        ⟨⟨homOfLE le_top⟩, fun _ ↦ Subsingleton.elim _ _⟩
      exact ((FreeAbelianGroup.uniqueEquiv _).trans AddEquiv.ulift.symm).toAddCommGrpIso)
      (by
        intro U V f
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro a
        simp [FreeAbelianGroup.uniqueEquiv])
  let eS := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapIso e
  let eH : CategoryTheory.Sheaf.H' F (n + 1) ⊤ ≃+
      CategoryTheory.Sheaf.H.{u} F (n + 1) :=
    (CategoryTheory.Abelian.Ext.precompAddEquiv eS F (n + 1)).symm
  exact eH.injective.subsingleton

end TopCat.Sheaf
