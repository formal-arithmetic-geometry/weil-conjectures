/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison

/-! # The fixed Ext universe change with a bundled cohomology codomain

Source: Mathlib Ext.chgUniv and Stacks Project, Tag 03FD.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

/-- The underlying function of Ext universe change, with its bundled target kept irreducible.
Source: Mathlib Ext.chgUniv and the fixed comparison of Stacks Project, Tag 03FD.
(blueprint: def-pbc-module-abelian-universe-equiv). -/
@[irreducible]
def moduleAbelianUniverseMap (X : Scheme.{u}) (F : X.Modules) (q : ℕ) :
    H F q → CoherentEtale.Source X F q :=
  fun x ↦ @coherentExtUniverseEquiv _ _ _ (comparisonHasExt X) (HasExt.standard _) _ _ q x

end
end AlgebraicGeometry.Scheme.Modules
