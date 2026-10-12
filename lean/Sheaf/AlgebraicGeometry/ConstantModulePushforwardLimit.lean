/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.ConstantModulePushforwardFunctoriality

/-!
# Constant module direct images on an inverse limit

Source: Stacks Project, Tag 09Z1 in degree zero.
(blueprint: lem-weil-pbc-constant-module-pushforward-limit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {X : Scheme.{u}} {I : Type u} [SmallCategory I]
    (D : I ⥤ Scheme.{u}) (p : ∀ i, D.obj i ⟶ X)
    (hp : ∀ {i j : I} (g : i ⟶ j), D.map g ≫ p j = p i)

/-- The filtered-direction diagram of direct images of constant modules. -/
noncomputable def constantModulePushforwardDiagram :
    Iᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj i := (lowerStar (ModuleCat.{u + 1} Λ) (p i.unop)).obj
    ((constantSheaf (D.obj i.unop).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  map g := constantModulePushforwardMap Λ M _ _ (D.map g.unop) (hp g.unop)
  map_id i := by
    dsimp
    simp only [D.map_id]
    exact (constantModulePushforwardMap_id_comp Λ M).1 _
  map_comp g g' := by
    dsimp
    simp only [D.map_comp]
    exact (constantModulePushforwardMap_id_comp Λ M).2 _ _ _ _ _ _ _

variable {Y : Scheme.{u}} (ν : Y ⟶ X)
    (π : (Functor.const I).obj Y ⟶ D) (hπ : ∀ i, π.app i ≫ p i = ν)

/-- The cone projections give a cocone on direct images of constant modules. -/
noncomputable def constantModulePushforwardCocone :
    Cocone (constantModulePushforwardDiagram Λ M D p hp) where
  pt := (lowerStar (ModuleCat.{u + 1} Λ) ν).obj
    ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  ι := {
    app i := constantModulePushforwardMap Λ M _ _ (π.app i.unop) (hπ i.unop)
    naturality {i j} g := by
      dsimp [constantModulePushforwardDiagram]
      rw [Category.comp_id]
      rw [← (constantModulePushforwardMap_id_comp Λ M).2]
      congr 1
      simpa using (π.naturality g.unop).symm }

/-- The canonical cocone for an affine cofiltered inverse system with qcqs structure
maps is a colimit of constant-module direct images.

Source: Stacks Project, Tag 09Z1, degree zero, and Tag 09Z6, finite approximation paragraph.
(blueprint: lem-weil-pbc-constant-module-pushforward-limit).

Proof: Replace the small cofiltered category by a small coinitial directed preorder
and pull the scheme limit and the sheaf diagrams along that functor. For each stage,
the inverse image of its constant M-sheaf on the limit is canonically the constant
M-sheaf. The transition maps under these comparisons are identities, by the defining
pullback comparison. Their colimit is thus constant M, since a filtered category is
nonempty and connected. All transition morphisms are affine and all structure maps
are qcqs by hypothesis, so Tag 09Z1 in degree zero makes the canonical comparison
from the colimit of stage direct images to the direct image on the limit an isomorphism
on underlying abelian sheaves. Its components are precisely the maps defining the
cocone here, by the inverse-image adjunction. The module structures are respected:
every component is linear, and forgetting modules creates filtered colimits of
sheaves (sheafify sectionwise filtered module colimits, whose underlying groups are
the corresponding filtered group colimits). Thus the comparison is an isomorphism
of module sheaves and the cocone is a colimit. Coinitiality of the inverse indexing
functor becomes finality in the filtered direction and transfers the colimit back.
No finiteness assumption on the ring or module is needed, and the zero module and
empty limit scheme are covered by the same argument. -/
theorem isColimit_constantModulePushforwardCocone [IsCofiltered I]
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, QuasiCompact (p i)] [∀ i : I, QuasiSeparated (p i)]
    [QuasiCompact ν] [QuasiSeparated ν]
    (hc : IsLimit (Cone.mk Y π)) :
    Nonempty (IsColimit (constantModulePushforwardCocone Λ M D p hp ν π hπ)) := by sorry

end AlgebraicGeometry.Etale
