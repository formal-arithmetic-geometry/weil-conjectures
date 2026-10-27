/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Local properness of the canonical relative Proj

Source: Stacks Project, Morphisms, Lemmas 01WB and 01WC.
The missing argument identifies the relative Proj of the restricted module on an affine open
with the corresponding pullback chart of the global relative Proj, then transports the
H-projective properness of the affine finite-generator presentation across that comparison.
(blueprint: lem-trf-canonical-relative-proj-proper-local).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- The canonical relative Proj is proper after restriction to any affine open of the base.

Source: Stacks Project, Morphisms, Lemmas 01WB and 01WC.
Proof plan: choose the finite-generator affine presentation supplied by
`exists_affine_projectiveBundle_presentations`; its local relative Proj is H-projective and
therefore proper by `hProjective_properness`.  The normalized symmetric-algebra pullback
comparison identifies this local morphism with the restriction of the global canonical
relative Proj, and properness is invariant under the resulting arrow isomorphism.  The
comparison is the only postponed step.
(blueprint: lem-trf-canonical-relative-proj-proper-local). -/
theorem canonicalRelativeProj_restrict_proper {S : Scheme.{u}} (E : S.Modules)
    (hE : E.IsQuasiCoherentFiniteType) (U : S.Opens) (hU : IsAffineOpen U) :
    IsProper ((@SymmetricAlgebraSheaf.gradedAlgebraData S E hE.1).relProjHom ∣_ U) := by
  sorry

end AlgebraicGeometry

end
