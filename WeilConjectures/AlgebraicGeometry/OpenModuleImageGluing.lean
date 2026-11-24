/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
import WeilConjectures.AlgebraicGeometry.OpenModuleImageAmalgamation
import WeilConjectures.AlgebraicGeometry.OpenModuleImageSeparated

/-! # Gluing the concrete open restriction/direct-image units

## References

* Stacks Project, Cohomology, Tag 08BV.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false

namespace AlgebraicGeometry

/-- The restriction units for a two-open cover form a pullback, for every module sheaf.
(Stacks, Tags 08BV and 01EB) -/
theorem schemeOpenModuleImage_isPullback
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    IsPullback ((schemeOpenModuleAdjunction X U).unit.app M)
      ((schemeOpenModuleAdjunction X V).unit.app M)
      ((schemeOpenModuleImageRestriction X (homOfLE (inf_le_left : U ⊓ V ≤ U))).app M)
      ((schemeOpenModuleImageRestriction X (homOfLE (inf_le_right : U ⊓ V ≤ V))).app M) := by
  have comm :
      (schemeOpenModuleAdjunction X U).unit.app M ≫
          (schemeOpenModuleImageRestriction X
            (homOfLE (inf_le_left : U ⊓ V ≤ U))).app M =
        (schemeOpenModuleAdjunction X V).unit.app M ≫
          (schemeOpenModuleImageRestriction X
            (homOfLE (inf_le_right : U ⊓ V ≤ V))).app M := by
    rw [schemeOpenModuleImage_unit_restriction X
      (homOfLE (inf_le_left : U ⊓ V ≤ U)) M]
    rw [schemeOpenModuleImage_unit_restriction X
      (homOfLE (inf_le_right : U ⊓ V ≤ V)) M]
  refine IsPullback.of_isLimit' ⟨comm⟩ ?_
  let lift : ∀ s : PullbackCone
      ((schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_left : U ⊓ V ≤ U))).app M)
      ((schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_right : U ⊓ V ≤ V))).app M),
      s.pt ⟶ M := fun s ↦
    (schemeOpenModuleImage_pullback_exists X U V hcover M s.fst s.snd
      s.condition).choose
  apply PullbackCone.IsLimit.mk comm lift
  · intro s
    exact (schemeOpenModuleImage_pullback_exists X U V hcover M s.fst s.snd
      s.condition).choose_spec.1
  · intro s
    exact (schemeOpenModuleImage_pullback_exists X U V hcover M s.fst s.snd
      s.condition).choose_spec.2
  · intro s m hm₁ hm₂
    apply schemeOpenModuleImage_pullback_unique X U V hcover M
      (hm₁.trans ((schemeOpenModuleImage_pullback_exists X U V hcover M s.fst s.snd
        s.condition).choose_spec.1).symm)
      (hm₂.trans ((schemeOpenModuleImage_pullback_exists X U V hcover M s.fst s.snd
        s.condition).choose_spec.2).symm)

end AlgebraicGeometry
