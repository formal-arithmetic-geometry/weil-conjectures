/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Residue-field fibres of scheme modules

Source: Stacks Project, Modules, Tags 01C5 and 01CB; Sheaves, Tag 0098
(blueprint: def-weil-pbc-module-residue-fiber).

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.residueFiber`: the stalk extended to the residue field.
- `AlgebraicGeometry.Scheme.Modules.residueValue`: the value of a section in that fibre.
-/

universe u

open CategoryTheory
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- The fibre `κ(x) ⊗_{O_{X,x}} M_x`, equivalently `M_x ⊗_{O_{X,x}} κ(x)`.
Source: Stacks Project, Modules, Tag 01C5; Sheaves, Tag 0098
(blueprint: def-weil-pbc-module-residue-fiber). -/
def residueFiber {X : Scheme.{u}} (M : X.Modules) (x : X) : ModuleCat (X.residueField x) :=
  (ModuleCat.extendScalars (X.residue x).hom).obj
    (ModuleCat.of (X.presheaf.stalk x) (M.presheaf.stalk x))

/-- A section's value in the fibre is its germ tensored with `1`.
Source: Stacks Project, Modules, Tag 01C5; Sheaves, Tag 0098
(blueprint: def-weil-pbc-module-residue-fiber). -/
def residueValue {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}
    (s : Γ(M, U)) (x : X) (hx : x ∈ U) : residueFiber M x :=
  (1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x, (X.residue x).hom]
    M.presheaf.germ U x hx s

end
end AlgebraicGeometry.Scheme.Modules
