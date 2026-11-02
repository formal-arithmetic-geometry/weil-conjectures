/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData

/-! # Compact-support composition in the current standing field setting

Source: current sk-thm-sf-comp-composition, clauses (1)--(2), including the normalization
by the proper/open interchange and its coherence laws
(blueprint: sk-thm-sf-comp-composition).

Reuse the published data structure, which records actual ambient arrows on Loc, preservation
of Dctf, the refinement normalization, units, associativity and arbitrary base change.
The current node explicitly assumes that the base field is finite or algebraically closed.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing.CompactSupportComposition

/-- Coherent composition and Cartesian exchange on the ordinary localizing closures,
restricting to bounded constructible finite-Tor objects, in the current field setting.
The existing `CoherentData` structure pins composition to proper/open interchange and exchange
to proper base change followed by open exchange and compactification comparison.
Source: current sk-thm-sf-comp-composition, all clauses and normalization paragraph
(blueprint: sk-thm-sf-comp-composition).

Proof: (1) Nagata compactification and preservation by proper image and open extension
provide the ordinary functors on Loc and Dctf. (2) Interchange the middle proper and open
factors by the unique identity-on-the-open map and apply the proper/open compositors.
(3) Common dense refinements and their cocycle compare all compactifications; mate
pasting commutes with refinement. (4) Expanding three factors and the identity models
gives associativity and both unit equations. (5) Proper base change is invertible on
Dctf, then on Loc by compact generation; pullback preserves the generators and coproducts.
The finite or algebraically closed base has the required finite ell-cohomological dimension.
(6) Pull back a compactification and compose proper exchange with inverse open exchange
and the comparison to the chosen model. Refinement gives independence.
(7) Mixed mate pasting gives compatibility with composing Cartesian squares and with
composition. Fullness restricts every comparison and equality to Dctf. -/
theorem coherent_exists_current (ell p : ℕ) [Fact ell.Prime] [Fact p.Prime]
    (hpell : p ≠ ell) (k : Type u) [Field k] [CharP k p]
    (_hk : Finite k ∨ IsAlgClosed k)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ell Λ) :
    Nonempty (CoherentData Λ k) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.CompactSupportComposition
