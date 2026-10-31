/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.PostnikovAdditiveExactCoupleData

/-! # Natural additive half-plane abutment

Source: Stacks Project, Homology, Tags 012F and 012U.
-/

@[expose] public section

set_option autoImplicit false

universe u v w uB vB

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]

/-- The half-plane Postnikov abutments and their filtrations are natural and additive.

Source: Stacks Project, Homology, Tags 012F and 012U
(blueprint: lem-per-postnikov-natural-abutment).

Proof: For each half-plane object apply halfPlaneConvergence with its own lower bound.
This supplies limiting subobjects, the normalized diagonal colimits with object D(0,n),
and convergence. Compose the normalized abutment identification with C.dIso at (0,n).
The alpha squares of P.map at page zero give a map of diagonal cocones; the colimit
universal property gives its unique abutment map. Evaluate its square at index zero
to identify this map with the conjugate of postnikovD.map. The image squares restrict
this map to each filtration step; passing adjacent-step squares to cokernels gives
its graded map. Monic cancellation on steps and epic cancellation on quotients prove
the functor laws and additivity. Restrict the initial E-map to limiting cycles and
descend modulo limiting boundaries, using derivedCoupleFunctoriality. This defines
the additive infinity functor and its defining quotient square. The canonical
infinity/graded comparison supplied by half-plane convergence commutes with these maps:
both composites agree after the canonical epimorphism from D. Finally choose a cutoff
past both half-plane differential bounds. The stationary cycle and boundary quotients
give stableIso; their defining projections give stable_projection and stable_natural.
Different cutoffs of source and target are handled on one common larger finite page. -/
theorem exists_postnikov_abutment_data {T : DerivedCategory A ⥤ B}
    {C : PostnikovCoupleData T} (P : PostnikovPageData C) :
    Nonempty (PostnikovAbutmentData P) := by sorry

end DerivedCategory
