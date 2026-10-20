/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPresheafOpenPullback

/-! Auxiliary homotopy data for exterior sheaf restriction.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
(blueprint: lem-sc-exterior-sheaf-restrict-hom-data).
-/

@[expose] public section

universe v

open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- The two sectionwise constructions have the same restriction maps by uniqueness on wedges. -/
private theorem exteriorSheafPresheaf_eq_exteriorPower {X : Scheme.{v}}
    (M : X.Modules) (n : ℕ) :
    exteriorSheafPresheaf M n = _root_.PresheafOfModules.exteriorPower M.val n := by
  have hmap : ∀ {V W : X.Opensᵒᵖ} (f : V ⟶ W),
      exteriorSheafRestriction M n f =
        (_root_.PresheafOfModules.exteriorPower M.val n).map f := by
    intro V W f
    apply ((Classical.choose_spec (exteriorSheafRestriction_existsUnique M n f)).2 _ ?_).symm
    intro a
    exact _root_.PresheafOfModules.exteriorPower_map_ιMulti M.val n f a
  unfold exteriorSheafPresheaf _root_.PresheafOfModules.exteriorPower
  congr 1
  funext V W f
  exact hmap f

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
  have hp := exteriorPresheaf_open_pullback M n U
  rw [← exteriorSheafPresheaf_eq_exteriorPower M n,
    ← exteriorSheafPresheaf_eq_exteriorPower (M.restrict U.ι) n] at hp
  obtain ⟨p⟩ := hp
  let a := (restrictFunctorIsoPullback U.ι).app (exteriorSheaf M n)
  let b := (SheafOfModules.sheafificationCompPullback.{v}
    U.ι.toRingCatSheafHom).app (exteriorSheafPresheaf M n)
  let c := (PresheafOfModules.sheafification.{v}
    (𝟙 U.toScheme.ringCatSheaf.obj)).mapIso p
  let e : (exteriorSheaf M n).restrict U.ι ≅ exteriorSheaf (M.restrict U.ι) n :=
    a ≪≫ b ≪≫ c
  exact ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

end AlgebraicGeometry.Scheme.Modules
