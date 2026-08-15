/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Subschemes attached to equal ideal sheaves

The inclusions of the subschemes attached to equal ideal sheaves agree up to `eqToHom`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {Y : Scheme.{u}}

/-- The inclusions of the subschemes attached to equal ideal sheaves agree up to
`eqToHom`. -/
lemma eqToHom_comp_subschemeι {I J : Y.IdealSheafData} (e : I = J) :
    eqToHom (congrArg subscheme e) ≫ J.subschemeι = I.subschemeι := by
  subst e
  simp

end AlgebraicGeometry.Scheme.IdealSheafData
