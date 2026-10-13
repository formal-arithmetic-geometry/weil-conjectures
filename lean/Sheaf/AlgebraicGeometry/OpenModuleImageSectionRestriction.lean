/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module
public import Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisData
/-! # Evaluation of the transported nested-open restriction

Source: Stacks Project, Cohomology, Tag 08BV.
(blueprint: lem-pc-open-module-image-section-restriction).
-/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
namespace AlgebraicGeometry

/-- The overlap mate is ordinary restriction after the open-site comparisons.
Source: Stacks Project, Cohomology, Tag 08BV (lemma-exact-sequence-j-star),
sectionwise sequence, with the concrete maps of
`schemeOpenModuleImageRestriction`.
(blueprint: lem-pc-open-module-image-section-restriction)
Proof: Expand the mate into the smaller restriction unit, the inverse
composition comparison, the restricted larger counit, and the forward
composition comparison. Insert overFunctorEquiv on both ends. Its inverse
and forward components cancel. The unit and counit of overEquiv cancel by
the equivalence triangle identity, and overFunctorMap has identity section
components. The remaining ordinary unit and counit components are restriction
maps by restrictAdjunction_unit_app_app and restrictAdjunction_counit_app_app.
Functoriality combines them into the single restriction along
W ∩ T ⊆ U ∩ T. The opens written as image-preimages below equal these
intersections by image_preimage_eq_opensRange_inf and opensRange_ι.
This computation holds for all nested opens, including the empty and equal
ones, and uses no covering hypothesis or sheaf amalgamation.
-/
theorem schemeOpenModuleImage_section_restriction
    (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (T : X.Opens)
    (a : ((schemeOpenModuleImage X U).obj M).val.obj (.op T)) :
    (((Scheme.Modules.pushforward W.ι).map
      ((Scheme.Modules.overFunctorEquiv W).hom.app M)).val.app (.op T))
      (((schemeOpenModuleImageRestriction X i).app M).val.app (.op T) a) =
    M.val.map (homOfLE (show W.ι ''ᵁ (W.ι ⁻¹ᵁ T) ≤ U.ι ''ᵁ (U.ι ⁻¹ᵁ T) by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        Scheme.Opens.opensRange_ι]
      exact inf_le_inf_right T (leOfHom i))).op
      ((((Scheme.Modules.pushforward U.ι).map
        ((Scheme.Modules.overFunctorEquiv U).hom.app M)).val.app (.op T)) a) := by
  sorry
end AlgebraicGeometry
