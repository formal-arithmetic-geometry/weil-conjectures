/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DualNumbers
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Group.Action.Hom

/-! # Marked identity-reducing automorphisms over the dual numbers

Source: Stacks Project, more-morphisms.tex, Tag 02H5, and curves.tex, section-vector-fields
(blueprint: def-sfb-marked-infinitesimal-automorphisms).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The subgroup of scheme automorphisms fixing a specified map into their source, by
postcomposition. This is Mathlib's stabilizer for the action through `Aut.toEnd`.
Source: Stacks Project, more-morphisms.tex, Tag 02H5, automorphisms with fixed restriction
(blueprint: def-sfb-marked-infinitesimal-automorphisms). -/
def Scheme.mapFixingAutomorphisms {X Y : Scheme.{u}} (s : Y ⟶ X) : Subgroup (Aut X) :=
  @MulAction.stabilizer (Aut X) (Y ⟶ X) _
    (MulAction.compHom (Y ⟶ X) (Aut.toEnd X)) s

/-- Automorphisms of the constant dual-number thickening over the dual-number base,
reducing to the identity and fixing every constant marked section. The thickening is the
existing `Scheme.dualNumbers`; for `Spec k` its base is canonically `Spec (DualNumber k)`
by `dualNumbersToSpec`. No automorphism is required to fix the projection to `X`.
Source: Stacks Project, more-morphisms.tex, Tag 02H5, split thickening, and curves.tex,
section-vector-fields (blueprint: def-sfb-marked-infinitesimal-automorphisms). -/
def markedInfinitesimalAutomorphisms {X S : Scheme.{u}} (f : X ⟶ S) {n : ℕ}
    (p : Fin n → (S ⟶ X)) : Subgroup (Aut (Over.mk f.dualNumbers)) :=
  ((Scheme.mapFixingAutomorphisms X.dualNumbersι) ⊓
    ⨅ i : Fin n, Scheme.mapFixingAutomorphisms (p i).dualNumbers).comap
      ((Over.forget S.dualNumbers).mapAut (Over.mk f.dualNumbers))

end AlgebraicGeometry
