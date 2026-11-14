/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSystems

/-! # Share the actual Kummer complex and its positive boundary
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable {l : ℕ} [Fact l.Prime] {T : Scheme.{u}}

/-- The actual Kummer arrows as a short complex for the named Abelian structure.

The construction uses the recorded inclusion, power and zero relation.
Its named exactness and boundary share those same arrows at every use. -/
abbrev Kummer.shortComplex (q : Kummer l T) :=
  ShortComplex.mk q.inclusion q.power q.zero

/-- The shared complex retains the exactness recorded by the Kummer data. -/
theorem Kummer.shortComplex_exact (q : Kummer l T) : q.shortComplex.ShortExact := by
  exact q.exact

/-- The positive Kummer boundary with its literal tower endpoints.
This is the derived boundary of the recorded short exact sequence. -/
def Kummer.boundary (q : Kummer l T) :
    (DerivedCategory.singleFunctor (Ab T) 0).obj (units T) ⟶
      ((DerivedCategory.singleFunctor (Ab T) 0).obj (roots l T))⟦(1 : ℤ)⟧ :=
  ShortComplex.ShortExact.singleδ (S := q.shortComplex) q.shortComplex_exact

end AlgebraicGeometry.ProEtale.SpTowerClasses
