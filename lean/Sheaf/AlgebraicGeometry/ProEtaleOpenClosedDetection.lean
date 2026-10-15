/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Mathlib.Algebra.Homology.ExactSequence
import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction

/-!
# Detection by open and closed pro-etale restrictions

Source: Weil conjectures blueprint, smooth purity, `sk-prop-sf-closed-unit`,
`lem-exc-open-closed-detection`; Stacks Project, Tag 09AH, lemma-ses-associated-to-open
(blueprint: lem-exc-open-closed-detection).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A module over arbitrary commutative ring-sheaf coefficients is zero if its pullbacks
along a closed immersion and its complementary quasi-compact open immersion are zero.
The coefficient isomorphisms are specified, and pullback uses the recorded tensor extension.

Source: Stacks Project, Tag 09AH, lemma-ses-associated-to-open; blueprint smooth purity,
`sk-prop-sf-closed-unit` (blueprint: lem-exc-open-closed-detection).

Proof:
1. Transport the actions back along `ci` and `cj`. By
   def-weil-pbc-proetale-operations, tensor extension along a coefficient isomorphism
   identifies pullback with inverse image: send `m ⊗ r` to `c.inv(r) m`, with inverse
   `m ↦ m ⊗ 1`. Balancing gives the inverse identities, naturally under restrictions.
   Thus the two ordinary module inverse images vanish, without any finiteness or
   constancy hypothesis on the coefficient sheaf.
2. Apply lem-weil-pbc-proetale-ringed-open-closed to the closed immersion and its
   quasi-compact open complement. Its actual counit and unit form the short exact
   sequence `0 → j_! j⁻¹ F → F → i_* i⁻¹ F → 0`. Transport the open restriction through
   the localized-site equivalence in that theorem. No qcqs hypothesis on X is needed
   for this sequence; its additional filtered-colimit assertion is not used.
3. The closed end term is zero by the sectionwise direct-image formula in
   def-weil-pbc-proetale-operations. The open end term is zero since the adjunction
   `j_! ⊣ j⁻¹` identifies maps out of `j_! 0` with maps out of zero, making it initial
   and hence zero. Exactness at F, in def-weil-pbc-exact-sequence, now identifies the
   zero image with the whole kernel of `F → 0`. Consequently F is zero. -/
theorem proEtaleRingModule_isZero_of_open_closed
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (Ri : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (Rj : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (ci : (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R ≅ Ri)
    (cj : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ Rj)
    (F : proEtaleRingModules X R)
    (hj : IsZero ((proEtaleRingModulePullback j R Rj cj).obj F))
    (hi : IsZero ((proEtaleRingModulePullback i R Ri ci).obj F)) : IsZero F := by
  sorry

end AlgebraicGeometry.Scheme
