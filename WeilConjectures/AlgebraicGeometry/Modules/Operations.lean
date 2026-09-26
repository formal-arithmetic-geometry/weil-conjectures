/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

@[expose] public section

/-!
# Operations on sheaves of modules on a scheme that Mathlib does not have yet

Mathlib has a monoidal structure on `PresheafOfModules` but none on `SheafOfModules`, no dual of
a sheaf of modules and no notion of an ample invertible sheaf. All three are needed to state the
Picard-framework results of the blueprint — Serre duality, Serre's theorems A and B, the twist
lemma, the cohomology of projective space — so they are collected here as placeholders with
`sorry` bodies, each tagged for the later unification pass.

None of these is a real construction. They exist so that the blueprint statements can be written
in their natural form; filling them in is separate work.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

-- TODO(unify): sk-thm-picard-duality
/-- The tensor product of two sheaves of modules on a scheme: the sheafification of the
presheaf tensor product. Mathlib has the monoidal structure on `PresheafOfModules` but not on
`SheafOfModules`, so this is a placeholder. -/
noncomputable def tensorObj (M N : X.Modules) : X.Modules := sorry

@[inherit_doc] scoped infixl:70 " ⊗ₘ " => AlgebraicGeometry.Scheme.Modules.tensorObj

-- TODO(unify): sk-thm-picard-duality
/-- The dual `M^∨ = Hom(M, 𝒪_X)` of a sheaf of modules on a scheme. Placeholder: Mathlib has no
internal hom for `SheafOfModules`. -/
noncomputable def dual (M : X.Modules) : X.Modules := sorry

/-- Notation for the dual of a sheaf of modules. -/
scoped postfix:max "ᵛ" => AlgebraicGeometry.Scheme.Modules.dual

-- TODO(unify): sk-thm-picard-rr
/-- An invertible sheaf on a scheme is **ample** if the basic opens of its global sections cover
the scheme and are affine. Placeholder: Mathlib has no notion of ampleness. -/
def IsAmple (M : X.Modules) : Prop := sorry

end AlgebraicGeometry.Scheme.Modules
