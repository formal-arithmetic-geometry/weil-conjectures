/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Sheaf.CategoryTheory.SiteCoveringAxioms

/-! # Restriction-compatible alternating families

Source: Stacks Project, Algebra, Tag 00DM, and Modules on Sites, Tag 03CY,
finite-variable extension (blueprint: def-sfb-site-alternating-family).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace PresheafOfModules

set_option autoImplicit false

/-- A sectionwise alternating multilinear map commuting with every restriction.
For zero variables, an alternating map is a choice of an element; the condition
below is exactly compatibility of those elements with restriction.
Source: Stacks 00DM and 03CY (blueprint: def-sfb-site-alternating-family). -/
def SiteAlternatingFamily {C : Type u} [Category.{v} C]
    {A : Cᵒᵖ ⥤ CommRingCat.{w}}
    (P N : PresheafOfModules.{w} (A ⋙ forget₂ CommRingCat RingCat)) (n : ℕ) :=
  { b : ∀ U : Cᵒᵖ, AlternatingMap (A.obj U) (P.obj U) (N.obj U) (Fin n) //
    ∀ (U V : Cᵒᵖ) (f : U ⟶ V) (x : Fin n → P.obj U),
      b V (fun i ↦ P.map f (x i)) = N.map f (b U x) }

end PresheafOfModules
