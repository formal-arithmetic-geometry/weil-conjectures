/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.Sites.Torsor

/-!
# The free extension presentation of an etale torsor

Source: Stacks Project, Tag 03AJ, the free abelian sheaf construction
(blueprint: lem-sp-etale-torsor-extension-presentation-exists).
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace CategoryTheory.Sheaf.Torsor

set_option backward.isDefEq.respectTransparency.types false

variable (X : Scheme.{u})
variable {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (T : Torsor G)

namespace EtaleFreeExtension

/-- The free abelian sheaf on the sections of the torsor. -/
private noncomputable abbrev freeSheaf :=
  (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (T.sheaf.obj ⋙ AddCommGrpCat.free)

/-- The free abelian sheaf on pairs of sections. -/
private noncomputable abbrev relations :=
  (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (T.pairs ⋙ AddCommGrpCat.free)

/-- The relation sending `(x,y)` to `[y]-[x]`. -/
private noncomputable abbrev difference : relations X T ⟶ freeSheaf X T :=
  (presheafToSheaf _ _).map T.pairsDiff

/-- The relation sending `(x,y)` to the unique `g` with `g +ᵥ x = y`. -/
private noncomputable def displacement : relations X T ⟶ G :=
  ⟨sheafifyLift _ T.pairsSub G.property⟩

/-- The quotient of `G ⊕ ℤ[T]` by `[y]-[x] = y-x`, formed as a pushout. -/
private noncomputable abbrev extension := pushout (difference X T) (displacement X T)

/-- The inclusion of the coefficient sheaf in the presented extension. -/
private noncomputable abbrev inclusion : G ⟶ extension X T :=
  pushout.inr (difference X T) (displacement X T)

/-- The map of the free generators to the presented extension. -/
private noncomputable abbrev generators : freeSheaf X T ⟶ extension X T :=
  pushout.inl (difference X T) (displacement X T)

/-- The constant integer presheaf, in the coefficient universe of the torsor. -/
private abbrev integers : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1, 0} ℤ))

/-- Augmentation of the free abelian presheaf. -/
private def augmentation : T.sheaf.obj ⋙ AddCommGrpCat.free ⟶ integers X where
  app U := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun _ ↦ (⟨1⟩ : ULift.{u + 1, 0} ℤ))
  naturality U V f := by
    ext : 1
    refine FreeAbelianGroup.lift_ext _ _ fun t ↦ ?_
    change FreeAbelianGroup.lift _ (FreeAbelianGroup.map _ (FreeAbelianGroup.of t)) = _
    simp only [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of]
    rfl

private lemma difference_augmentation : T.pairsDiff ≫ augmentation X T = 0 := by
  ext U : 2
  ext : 1
  refine FreeAbelianGroup.lift_ext _ _ fun p ↦ ?_
  change FreeAbelianGroup.lift _ (FreeAbelianGroup.lift _ (FreeAbelianGroup.of p)) = 0
  simp only [FreeAbelianGroup.lift_apply_of, map_sub, _root_.sub_self]

/-- Augmentation of the free abelian sheaf. -/
private noncomputable abbrev degree : freeSheaf X T ⟶
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1, 0} ℤ)) :=
  (presheafToSheaf _ _).map (augmentation X T)

/-- The pair-difference relation has degree zero. -/
private lemma difference_degree : difference X T ≫ degree X T = 0 := by
  rw [← Functor.map_comp, difference_augmentation]
  exact (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map_zero _ _

/-- The degree of a section of the presented extension. -/
private noncomputable def projection : extension X T ⟶
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1, 0} ℤ)) :=
  pushout.desc (degree X T) 0 (by rw [difference_degree, comp_zero])

end EtaleFreeExtension

set_option backward.isDefEq.respectTransparency false in
end CategoryTheory.Sheaf.Torsor
