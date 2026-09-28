/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# The dual of a sheaf of modules on a scheme

Mathlib has no internal hom for `SheafOfModules`, hence no dual `M^∨ = Hom(M, 𝒪_X)`. Serre
duality and the twist lemma of the Picard-framework block both need it, so
`AlgebraicGeometry.Scheme.Modules.dual` is declared here as an `opaque` constant. Being
`opaque` rather than `sorry`-bodied it genuinely depends on its argument and introduces no `sorryAx`; but it
satisfies no equations whatsoever, so **no statement mentioning it can be proved before it is
replaced by the real construction**.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.dual`: the dual `M^∨` of a sheaf of modules (placeholder).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The dual `M^∨ = Hom(M, 𝒪_X)` of a sheaf of modules on a scheme.

Mathlib has no internal hom for `SheafOfModules`, so this is an `opaque` placeholder: it
satisfies no equations, and no statement mentioning it can be proved before it is replaced by
the real construction. -/
-- TODO(unify): sk-thm-picard-duality
opaque dual (M : X.Modules) : X.Modules := M

@[inherit_doc] scoped postfix:max "ᵛ" => AlgebraicGeometry.Scheme.Modules.dual

end AlgebraicGeometry.Scheme.Modules
