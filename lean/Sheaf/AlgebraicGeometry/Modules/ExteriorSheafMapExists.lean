/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf

/-!
# Exterior sheaf maps induced by module morphisms

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph,
exterior-power universal properties (blueprint: lem-sc-exterior-sheaf-map-exists).
-/

@[expose] public section

universe v
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

private theorem restriction_wedge {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    {U V : X.Opensᵒᵖ} (k : U ⟶ V) (a : Fin n → M.val.obj U) :
    exteriorSheafRestriction M n k (exteriorPower.ιMulti (X.presheaf.obj U) n a) =
      exteriorPower.ιMulti (X.presheaf.obj V) n (fun i ↦ M.val.map k (a i)) :=
  (Classical.choose_spec (exteriorSheafRestriction_existsUnique M n k)).1 a

set_option maxHeartbeats 800000 in
-- Comparing scheme ring-sheaf scalar structures requires additional elaboration.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Apply the sectionwise exterior-power functor to a module morphism. Naturality is checked
on pure wedges using naturality of the original morphism; pure wedges span the exterior
power. Sheafify this presheaf morphism. Naturality of the sheafification unit gives its
formula on wedge sections. No exactness or local freeness is required.
Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph,
exterior-power universal properties (blueprint: lem-sc-exterior-sheaf-map-exists). -/
theorem exteriorSheaf_map_exists {X : Scheme.{v}} {M N : X.Modules}
    (f : M ⟶ N) (n : ℕ) :
    ∃ e : exteriorSheaf M n ⟶ exteriorSheaf N n,
      ∀ (U : X.Opens) (a : Fin n → M.val.obj (op U)),
        e.val.app (op U) (exteriorSheafSection M n U a) =
          exteriorSheafSection N n U (fun i ↦ f.val.app (op U) (a i)) := by
  let p : exteriorSheafPresheaf M n ⟶ exteriorSheafPresheaf N n :=
    { app := fun U ↦ ModuleCat.ofHom (X := exteriorSheafObj M n U)
        (Y := exteriorSheafObj N n U)
        (exteriorPower.map (R := X.presheaf.obj U) n (f.val.app U).hom)
      naturality := by
        intro U V k
        apply ModuleCat.hom_ext
        apply exteriorPower.linearMap_ext (R := X.presheaf.obj U)
          (N := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map k).hom).obj
            (exteriorSheafObj N n V))
        apply DFunLike.ext
        intro a
        symm
        change exteriorSheafRestriction N n k
            (exteriorPower.map (R := X.presheaf.obj U) n (f.val.app U).hom
              (exteriorPower.ιMulti (X.presheaf.obj U) n a)) =
          exteriorPower.map (R := X.presheaf.obj V) n (f.val.app V).hom
            (exteriorSheafRestriction M n k
              (exteriorPower.ιMulti (X.presheaf.obj U) n a))
        rw [exteriorPower.map_apply_ιMulti (R := X.presheaf.obj U) (f.val.app U).hom a,
          restriction_wedge N n k, restriction_wedge M n k a]
        erw [exteriorPower.map_apply_ιMulti (R := X.presheaf.obj V)
          (f.val.app V).hom (fun i ↦ M.val.map k (a i))]
        apply congrArg (exteriorPower.ιMulti (X.presheaf.obj V) n)
        funext i
        exact (PresheafOfModules.naturality_apply f.val k (a i)).symm }
  refine ⟨(PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map p, ?_⟩
  intro U a
  have h := congrArg
    (fun k ↦ k.app (op U) (exteriorPower.ιMulti (X.presheaf.obj (op U)) n a))
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality p)
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (exteriorSheafPresheaf N n)).app (op U)
      (exteriorPower.map (R := X.presheaf.obj (op U)) n (f.val.app (op U)).hom
        (exteriorPower.ιMulti (X.presheaf.obj (op U)) n a)) =
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map p).val.app (op U)
      (exteriorSheafSection M n U a) at h
  rw [exteriorPower.map_apply_ιMulti (R := X.presheaf.obj (op U))
    (f.val.app (op U)).hom a] at h
  exact h.symm

end AlgebraicGeometry.Scheme.Modules
