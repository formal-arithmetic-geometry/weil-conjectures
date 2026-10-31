/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.TraceFormula.SchematicallyDenseOpen

/-! # Proper open immersions containing a schematically dense open

Source: Weil conjectures blueprint, main-20261015, Nagata compactification,
unit `sk-lem-nagata-sketch-near-closure`
(blueprint: lemma-nagata-proper-open-dense-iso).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A proper open immersion containing a schematically dense open is an isomorphism.
No quasi-compactness is imposed on the dense open.

Source: Weil conjectures blueprint, main-20261015, Nagata compactification,
`lemma-nagata-proper-open-dense-iso`; Stacks Tags 01W1, 01RB and 01RE
(blueprint: lemma-nagata-proper-open-dense-iso).

Proof plan: let V be the image of q. By `lem-weil-pbc-proper-closed-image`, V is
closed; by `def-weil-open-immersion`, it is open. Its open complement W is disjoint
from U. By `def-trf-schematically-dense-open`, restriction from every open A contained
in W to A intersect U is injective. The latter open is empty and its ring of sections
is the zero ring by the empty-cover sheaf axiom, so the sections on A are zero.
For any x in W, neighbourhoods contained in W are cofinal among its neighbourhoods;
hence the stalk at x is zero. This contradicts the nontrivial local ring condition
in `def-pc-scheme`. Thus W is empty and V is all of X. The open-immersion
identification of Z with the open subscheme V now makes q an isomorphism.
-/
theorem isIso_of_isProper_of_isOpenImmersion_of_schematicallyDenseOpen
    {X Z : Scheme.{u}} (q : Z ⟶ X) [IsProper q] [IsOpenImmersion q]
    (U : X.Opens) (hU : SchematicallyDenseOpen U) (hUq : U ≤ q.opensRange) : IsIso q := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply top_unique
  intro x _
  by_contra hx
  let W : X.Opens := ⟨(Set.range q)ᶜ, q.isClosedMap.isClosed_range.isOpen_compl⟩
  have hWU : W ⊓ U = ⊥ := by
    apply le_antisymm _ bot_le
    intro y hy
    exact (hy.1 (hUq hy.2)).elim
  have : Subsingleton Γ(X, W ⊓ U) := hWU ▸ inferInstance
  have h01 : (0 : Γ(X, W)) = 1 := by
    apply hU W
    exact Subsingleton.elim _ _
  have hW : Nonempty W := ⟨⟨x, hx⟩⟩
  have : Nontrivial Γ(X, W) :=
    LocallyRingedSpace.component_nontrivial X.toLocallyRingedSpace W (hU := hW)
  exact zero_ne_one h01

end AlgebraicGeometry
