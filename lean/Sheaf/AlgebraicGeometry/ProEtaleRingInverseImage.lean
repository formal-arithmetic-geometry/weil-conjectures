/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

/-!
# Inverse image for possibly noncommutative pro-etale ring sheaves

Source: Stacks Project, Tags 09A5, 00YV and 03D2
(blueprint: def-weil-proetale-inverse-image).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The ring adjunction unit transported to the existing small site model.
No commutativity is used. Source: Stacks, Tags 00YV and 03D2
(blueprint: def-weil-proetale-inverse-image). -/
noncomputable def proEtaleRingModelUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj R ⟶
    ((proEtaleModelBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (proEtaleModelTopology Y) (proEtaleModelTopology X)).obj
        (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
          RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj
            ((proEtaleSheafInverseImage f RingCat.{u + 1}).obj R)) :=
  ⟨Functor.whiskerLeft AsSmall.down.op
    ((proEtaleSheafAdjunction f RingCat.{u + 1}).unit.app R).hom⟩

/-- Inverse image of modules over any ring sheaf, with coefficients its ring inverse
image. This is the sheafified module Kan extension along the ring adjunction unit,
transported through the already defined small model and back to the original site.
The tensor in the module Kan extension uses right and left actions, so does not
require commutativity. Source: Stacks, Tags 00YV and 03D2
(blueprint: def-weil-proetale-inverse-image). -/
noncomputable def proEtaleRingModuleInverseImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    ringedSiteModules.{u + 1} R ⥤ ringedSiteModules.{u + 1}
      ((proEtaleSheafInverseImage f RingCat.{u + 1}).obj R) :=
  proEtaleModuleToModel R ⋙
    SheafOfModules.pullback (proEtaleRingModelUnit f R) ⋙
      proEtaleModuleFromModel ((proEtaleSheafInverseImage f RingCat.{u + 1}).obj R)

end AlgebraicGeometry.Scheme
