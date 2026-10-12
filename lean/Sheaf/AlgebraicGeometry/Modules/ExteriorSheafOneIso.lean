module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option maxHeartbeats 800000 in
-- Naturality elaborates restrictions across the scheme and ring-sheaf module interfaces.
/-- The first exterior sheaf is canonically isomorphic to the original sheaf.
Source: Stacks Project, Tag 0BRT, degree-one specialization; Mathlib
`exteriorPower.oneEquiv` and the sheafification adjunction.
(blueprint: lem-sc-smooth-proper-curve-dualizing-exterior-one)
Proof: on each open U, use `exteriorPower.oneEquiv` to send the singleton wedge of
m to m. For a restriction U to V, the chosen exterior restriction sends the singleton
wedge of m to the singleton wedge of its restriction, by
`exteriorSheafRestriction_existsUnique`. Thus the degree-one equivalences commute with
restrictions on singleton wedges, and on every element because these wedges span.
Their inverses also commute with restrictions, giving an isomorphism from
`exteriorSheafPresheaf M 1` to `M.val`. Apply the sheafification functor to this
isomorphism, then compose with the invertible counit of
`PresheafOfModules.sheafificationAdjunction` at M. Since M is already a sheaf, this
counit identifies the sheafification of `M.val` with M, proving the result.
-/
theorem exteriorSheaf_one_iso {X : Scheme.{u}} (M : X.Modules) :
    Nonempty (exteriorSheaf M 1 ≅ M) := by
  let e : exteriorSheafPresheaf M 1 ≅ M.val :=
    PresheafOfModules.isoMk
      (fun U ↦ (exteriorPower.oneEquiv (X.presheaf.obj U) (M.val.obj U)).toModuleIso)
      (by
        intro U V f
        ext x
        obtain ⟨m, rfl⟩ :=
          (exteriorPower.oneEquiv (X.presheaf.obj U) (M.val.obj U)).symm.surjective x
        change exteriorPower.oneEquiv (X.presheaf.obj V) (M.val.obj V)
            (exteriorSheafRestriction M 1 f
              ((exteriorPower.oneEquiv (X.presheaf.obj U) (M.val.obj U)).symm m)) =
          M.val.map f
            (exteriorPower.oneEquiv (X.presheaf.obj U) (M.val.obj U)
              ((exteriorPower.oneEquiv (X.presheaf.obj U) (M.val.obj U)).symm m))
        rw [LinearEquiv.apply_symm_apply, exteriorPower.oneEquiv_symm_apply]
        have h := (Classical.choose_spec
          (exteriorSheafRestriction_existsUnique M 1 f)).1 (fun _ ↦ m)
        exact (congrArg (exteriorPower.oneEquiv (X.presheaf.obj V) (M.val.obj V)) h).trans
          (exteriorPower.oneEquiv_ιMulti _))
  exact ⟨(PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso e ≪≫
    asIso (C := SheafOfModules.{u} X.ringCatSheaf)
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app M)⟩

end AlgebraicGeometry.Scheme.Modules
