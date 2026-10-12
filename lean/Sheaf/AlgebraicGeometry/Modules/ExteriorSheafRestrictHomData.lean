/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
import Sheaf.AlgebraicGeometry.Modules.ExteriorPresheafOpenPullback

/-! Auxiliary homotopy data for exterior sheaf restriction.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
(blueprint: lem-sc-exterior-sheaf-restrict-hom-data).
-/

@[expose] public section

universe v

open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- The comparison between the restricted exterior sheaf and the exterior sheaf of the
restricted module has mutually inverse morphisms.
(blueprint: lem-sc-exterior-sheaf-restrict-hom-data)
The construction is by sheafifying the
sectionwise map carrying a pure wedge to the wedge of the corresponding restricted sections;
the inverse is obtained from the opposite sectionwise identification. The two composites are
checked on pure wedges, which generate exterior powers, and hence descend through sheafification.
-/
theorem exteriorSheaf_restrict_hom_data {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) : ∃ (e : (exteriorSheaf M n).restrict U.ι ⟶ exteriorSheaf (M.restrict U.ι) n),
      ∃ f : exteriorSheaf (M.restrict U.ι) n ⟶ (exteriorSheaf M n).restrict U.ι,
        e ≫ f = 𝟙 _ ∧ f ≫ e = 𝟙 _ := by
  obtain ⟨p⟩ := exteriorPresheaf_open_pullback M n U
  let a := (restrictFunctorIsoPullback U.ι).app (exteriorSheaf M n)
  let b := (SheafOfModules.sheafificationCompPullback.{v}
    U.ι.toRingCatSheafHom).app (exteriorSheafPresheaf M n)
  let c := (PresheafOfModules.sheafification.{v}
    (𝟙 U.toScheme.ringCatSheaf.obj)).mapIso p
  let e : (exteriorSheaf M n).restrict U.ι ≅ exteriorSheaf (M.restrict U.ι) n :=
    a ≪≫ b ≪≫ c
  exact ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

end AlgebraicGeometry.Scheme.Modules
