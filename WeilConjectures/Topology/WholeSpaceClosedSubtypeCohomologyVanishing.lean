/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Category.Grp.AB

import WeilConjectures.Topology.ClosedImmersionPushforwardCohomology
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Passing from the whole closed subtype to the ambient space

If cohomology vanishes on the whole space viewed as a closed subtype of itself, it vanishes on
the space.

## Implementation details

The subtype inclusion `i` has continuous inverse `j`, and `i_* j_* F ≅ F`; the closed-pushforward
comparison then transports vanishing. `Ext` change-of-universe equivalences transfer
subsingletonness between the small `Ext` groups in the statement and the standard `Ext` model.

## References

* [Stacks Project, Tag 02UV](https://stacks.math.columbia.edu/tag/02UV)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

/-- Universal vanishing on the whole closed subtype implies ambient vanishing. -/
theorem cohomology_vanishing_of_whole_closed_subtype
    (X : Type u) [TopologicalSpace X] (q : ℕ)
    (h : ∀ G : CategoryTheory.Sheaf (Opens.grothendieckTopology (Set.univ : Set X))
      AddCommGrpCat.{u}, IsZero (CategoryTheory.Sheaf.H' G q
        (⊤ : Opens (Set.univ : Set X))))
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    IsZero (CategoryTheory.Sheaf.H' F q (⊤ : Opens X)) := by
  let i : TopCat.of ↥(Set.univ : Set X) ⟶ TopCat.of X :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let j : TopCat.of X ⟶ TopCat.of ↥(Set.univ : Set X) :=
    TopCat.ofHom ⟨fun x ↦ ⟨x, Set.mem_univ x⟩, continuous_id.subtype_mk _⟩
  let G : CategoryTheory.Sheaf (Opens.grothendieckTopology (Set.univ : Set X))
    AddCommGrpCat.{u} := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} j).obj F
  obtain ⟨e⟩ := cohomology_closed_immersion_pushforward i
    isClosed_univ.isClosedEmbedding_subtypeVal G q
  have hij : j ≫ i = 𝟙 (TopCat.of X) := by ext x; rfl
  let eF : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G ≅ F :=
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).preimageIso
      ((TopCat.Presheaf.Pushforward.comp j i F.obj).symm ≪≫
        TopCat.Presheaf.pushforwardEq hij F.obj ≪≫
          TopCat.Presheaf.Pushforward.id (X := TopCat.of X) F.obj)
  let : HasExt.{u + 1} (CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) := HasExt.standard _
  let eH := ((CategoryTheory.Sheaf.cohomologyPresheafFunctor.{u + 1}
    (Opens.grothendieckTopology X) q).mapIso eF).app
    (Opposite.op (⊤ : Opens X))
  let : HasExt.{u + 1} (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (Set.univ : Set X)) AddCommGrpCat.{u}) := HasExt.standard _
  have hGsmall := AddCommGrpCat.subsingleton_of_isZero (h G)
  change Subsingleton (CategoryTheory.Abelian.Ext.{u} _ G q) at hGsmall
  let : Subsingleton (CategoryTheory.Sheaf.H'.{u + 1} G q
      (⊤ : Opens (Set.univ : Set X))) := by
    change Subsingleton (CategoryTheory.Abelian.Ext.{u + 1} _ G q)
    exact (CategoryTheory.Abelian.Ext.chgUniv.{u, u + 1}).subsingleton
  have hG : IsZero (CategoryTheory.Sheaf.H'.{u + 1} G q
      (⊤ : Opens (Set.univ : Set X))) := AddCommGrpCat.isZero_of_subsingleton _
  have hFbig := AddCommGrpCat.subsingleton_of_isZero (hG.of_iso (e ≪≫ eH).symm)
  change Subsingleton (CategoryTheory.Abelian.Ext.{u + 1} _ F q) at hFbig
  let : Subsingleton (CategoryTheory.Sheaf.H'.{u} F q (⊤ : Opens X)) := by
    change Subsingleton (CategoryTheory.Abelian.Ext.{u} _ F q)
    exact (CategoryTheory.Abelian.Ext.chgUniv.{u + 1, u}).subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

end TopCat
