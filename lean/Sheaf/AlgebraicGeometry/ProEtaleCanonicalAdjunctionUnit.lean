/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction

/-! The tensor-unit normalization of the constructed pro-etale module adjunction. -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] proEtaleRingModulePullback
  proEtaleRingDirectImageMap proEtaleRingModuleUnitSection

/-- The constructed Hom adjunction has the prescribed sectionwise tensor unit.
Source: Stacks 03D2 and 03D7
(blueprint: lem-pod-canonical-module-adjunction-unit).
Proof: apply the defining transpose formula to the identity of the pullback of M.
The resulting transpose is the adjunction unit. On the model site this transpose
is the model pullback unit followed by g. The defining formula for g sends its
input to the sheafification of 1 tensor that input. This is the stated unit
section, since the model equivalence preserves section carriers. -/
theorem proEtaleRingModuleAdjunction_normalized
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingModuleAdjunctionNormalized f R S c
      (proEtaleRingModuleAdjunction f R S c) := by
  intro M U m
  have hadj := (proEtaleRingModuleAdjunction_existsUnique f R S c).choose_spec.1
  obtain ⟨g, hg, he⟩ := hadj M _ (𝟙 _)
  have h := he (op U) m
  rw [Adjunction.homEquiv_id, Adjunction.homEquiv_unit] at h
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    CategoryTheory.comp_apply] at h
  change ((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app (op U) m =
    g.val.app (op (AsSmall.up.obj ((proEtaleBaseChange f).obj U)))
      (((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).unit.app
        ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M)).val.app
            (op (AsSmall.up.obj U)) m) at h
  refine h.trans ?_
  unfold proEtaleRingModuleUnitSection
  exact hg _ _

end AlgebraicGeometry.Scheme
