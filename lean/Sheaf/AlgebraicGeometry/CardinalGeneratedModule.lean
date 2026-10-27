/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.SetTheory.Cardinal.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Topology.PresheafModuleStalkFunctor

/-!
# Locally cardinal-generated module sheaves

Source: Stacks Project, Properties, Tag 077L, definition-kappa-generated
(blueprint: def-sfb-cardinal-generated-module).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- Local generation by at most `κ` sections: on an open covering, the germs of
these sections span every stalk. For infinite `κ` this is exactly Stacks Tag 077L,
`definition-kappa-generated`; the same formula also makes sense for finite cardinals.
(blueprint: def-sfb-cardinal-generated-module). -/
def IsCardinalGenerated {X : Scheme.{u}} (F : X.Modules) (κ : Cardinal.{u}) : Prop :=
  ∃ C : Set X.Opens, sSup C = ⊤ ∧
    ∀ U ∈ C, ∃ S : Set (F.val.obj (op U)), Cardinal.mk S ≤ κ ∧
      ∀ (x : X) (hx : x ∈ U),
        Submodule.span (X.presheaf.stalk x)
          ((fun s : F.val.obj (op U) ↦
            TopCat.Presheaf.germ (X := X.toTopCat) F.val.presheaf U x hx s) '' S) = ⊤

end AlgebraicGeometry.Scheme.Modules
