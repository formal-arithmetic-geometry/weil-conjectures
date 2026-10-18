/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

/-!
# The canonical projection map for condensed module objects

Source: blueprint main-20261015, sk-thm-sf-pf-adic-projection, projection map;
Stacks Project, Tags 03EL and 0943 (blueprint: def-sfb-module-object-projection-map).

The published module-object pullback tensor comparison is constructed on signed
K-flat total tensors and characterized by its derived counits. Its existing
right-adjoint mate gives the required map, without choosing a map between endpoints.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical projection map: the adjoint transpose of the generic K-flat
pullback tensor comparison followed by counit tensor identity.
Source: blueprint sk-thm-sf-pf-adic-projection; Stacks 0943
(blueprint: def-sfb-module-object-projection-map). -/
def moduleObjectProjectionMap
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :=
  (((derivedUpperStarLowerStarAdjunction Λ f).rightAdjointProjectionMap
    (T_C := derivedTensor Λ X) (T_D := derivedTensor Λ Y)
    (leftDerivedUpperStarTensor Λ f)).app K).app L

end AlgebraicGeometry.ProEtale.CondensedRing
