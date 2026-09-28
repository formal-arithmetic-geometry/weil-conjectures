/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Subquotients of a representation

`Mathlib.RepresentationTheory.Subrepresentation` provides the lattice `Subrepresentation ρ` of
subrepresentations of `ρ : Representation k W V` and, for a single subrepresentation `S`, the
representation `S.toRepresentation` on `S`.  This file adds the subquotient: for
subrepresentations `U ≤ S` the representation of `W` on `S ⧸ U`.

`U` is presented inside `S` as `U.toSubmodule.comap S.toSubmodule.subtype`, so that no inclusion
`U ≤ S` is needed to *form* the quotient; the interesting case is of course `U ≤ S`, where the
quotient is the honest subquotient `S / U`.

## Main declarations

* `Subrepresentation.subquotient`: the representation of `W` on `S ⧸ U`.
-/

@[expose] public section

namespace Subrepresentation

variable {k : Type*} [Field k] {W : Type*} [Group W]
variable {V : Type*} [AddCommGroup V] [Module k V] {ρ : Representation k W V}

/-- The representation induced on the subquotient `S ⧸ U` of two subrepresentations of `ρ`. -/
noncomputable def subquotient (S U : Subrepresentation ρ) :
    Representation k W (S.toSubmodule ⧸ U.toSubmodule.comap S.toSubmodule.subtype) where
  toFun w := Submodule.mapQ _ _ ((ρ w).restrict (S.apply_mem_toSubmodule w)) (by
    intro x hx
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hx ⊢
    simpa only [LinearMap.coe_restrict_apply] using U.apply_mem_toSubmodule w hx)
  map_one' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, map_one]
    exact congrArg _ (Subtype.ext (by simp))
  map_mul' v w := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, map_mul]
    exact congrArg _ (Subtype.ext (by simp))

end Subrepresentation
