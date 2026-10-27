/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic

/-! # Relative identity-component inclusions

Source: Bosch–Lütkebohmert–Raynaud, Néron Models, §10.1, Proposition 9
(blueprint: def-sfb-relative-identity-component).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

/-- An open subgroup inclusion identifies its source with the relative identity component
if its image on every geometric fibre is the connected component of the identity point.
The open immersion retains the full open-subscheme structure, including nilpotents.
Source: Bosch–Lütkebohmert–Raynaud, Néron Models, §10.1, Proposition 9
(blueprint: def-sfb-relative-identity-component). -/
def IsRelativeIdentityComponent {S : Scheme.{u}} {B N : Over S}
    [GrpObj B] [GrpObj N] (j : B ⟶ N) : Prop :=
  IsMonHom j ∧ IsOpenImmersion j.left ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      Set.range ((Over.pullback s).map j).left =
        connectedComponent (GrpObj.onePoint ((Over.pullback s).obj N))

end AlgebraicGeometry
