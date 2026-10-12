/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.SiteExtensionByZeroPresheaf
public import Mathlib.Topology.Sheaves.Stalks

/-! # Stalk isomorphism for the canonical nested slice map

Source: Stacks Project, Cohomology, Lemma 0A38 final paragraph; Sheaves, Lemma 00A5.
(blueprint: new-node-nested-slice-extension-stalk-iso).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory TopologicalSpace Opposite
namespace TopCat.Sheaf

/-- Canonical map from the slice extension over `V` to that over `U`. -/
noncomputable def nestedSliceExtensionMap {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X) (hVU : V ≤ U) :
    (siteExtensionByZeroPresheaf V).obj (F.over V).obj ⟶
      (siteExtensionByZeroPresheaf U).obj (F.over U).obj := by
  classical
  let : ∀ W : Opens X, DecidableEq (W ⟶ V) := fun _ _ _ ↦ Classical.propDecidable _
  let : ∀ W : Opens X, DecidableEq (W ⟶ U) := fun _ _ _ ↦ Classical.propDecidable _
  exact
    { app := fun W ↦ AddCommGrpCat.ofHom (DirectSum.toAddMonoid fun φ : W.unop ⟶ V ↦
        (DirectSum.of (fun ψ : W.unop ⟶ U ↦
          (F.over U).obj.obj (Opposite.op (Over.mk ψ))) (φ ≫ homOfLE hVU)).comp
            (AddMonoidHom.id _))
      naturality := by
        intro W Z a
        apply AddCommGrpCat.hom_ext
        apply DirectSum.addHom_ext
        intro φ x
        dsimp [siteExtensionByZeroPresheaf, siteExtensionByZeroPresheafObj,
          siteExtensionByZeroRestrict]
        erw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of,
          DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
        rw [Category.assoc]
        rfl }

/-- The canonical nested slice map induces an isomorphism on stalks over `V`.

Proof: neighborhoods contained in `V` are cofinal at points of `V`. On such a
neighborhood both indexing categories have a unique arrow, and the canonical map
is the identity on that unique summand. The standard germ description of stalks
then gives surjectivity and injectivity. This is the stalk argument of Stacks
Lemmas 0A38 and 00A5.
(blueprint: new-node-nested-slice-extension-stalk-iso). -/
theorem nestedSliceExtensionMap_stalk_isIso {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X) (hVU : V ≤ U) :
    ∀ x : X, x ∈ V →
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (nestedSliceExtensionMap F U V hVU)) := by
  sorry

end TopCat.Sheaf
