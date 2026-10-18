/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.EssentialImage
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Mathlib.Algebra.Homology.ExactSequence

/-!
# Essential image of closed direct image on pro-etale module sheaves

Source: blueprint smooth purity, `sk-prop-sf-closed-unit`,
`lem-exc-proetale-closed-essential-image`; Stacks Project, Pro-etale Cohomology,
Tag 09AH, `lemma-ses-associated-to-open`
(blueprint: lem-exc-proetale-closed-essential-image).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Closed direct image has precisely the module sheaves with zero open restriction as
its essential image. On these sheaves the canonical module adjunction unit is invertible.
The arbitrary commutative coefficient sheaves and their inverse-image identifications are
fixed explicitly; the unit is that of the tensor-unit-normalized adjunction.

Source: blueprint smooth purity, `sk-prop-sf-closed-unit`,
`lem-exc-proetale-closed-essential-image`; Stacks Project, Tag 09AH,
`lemma-ses-associated-to-open`
(blueprint: lem-exc-proetale-closed-essential-image).

Proof:
1. Normalize coefficients as in def-weil-pbc-proetale-operations. Tensor extension along
   ci or cj is scalar transport: m tensor a maps to c.inv(a)m, with inverse m maps to
   m tensor 1. The balancing relation proves both inverse identities. Transport an
   Ri-module back to an inverse-image-R-module by b acting as ci(b). Its direct-image
   R-action is unchanged, since the adjoint of ci becomes the inverse-image ring unit.
   These identifications are natural. If theta identifies tensor pullback with transported
   inverse image, adjunction transposition gives i_*(theta) composed with the actual
   identified-coefficient unit equal to the inverse-image-coefficient unit. Thus they
   preserve essential-image membership, zero restriction, and invertibility of this unit.
2. Apply lem-weil-pbc-proetale-ringed-open-closed to i and the complementary
   quasi-compact open immersion j. It supplies j inverse-image composed with i_* equal
   to zero, the adjunction j_! to j inverse-image, and the short exact sequence
   0 to j_! j inverse-image F to F to i_* i inverse-image F to 0. Its middle-to-right
   arrow is the closed adjunction unit. Its extra qcqs hypothesis on X belongs only to
   its filtered-colimit clause, which is not used here.
3. If F is isomorphic to i_*G, applying open inverse image identifies its restriction
   with j inverse-image i_*G, hence with zero.
4. Conversely, if the open restriction is zero, j_! of that restriction is zero: its
   maps into every module sheaf are singleton sets by the open adjunction. The sequence
   becomes 0 to 0 to F to i_* i inverse-image F to 0. Exactness gives zero kernel for
   the unit and says it is epic. In the abelian category of module sheaves, an epic map
   is a cokernel. Its zero kernel forces the map it cokernels to be zero, so the
   cokernel universal property factors the identity of F through the unit. Cancellation
   of the epic unit proves the other inverse identity. Hence the actual unit is invertible.
5. The inverse of that unit exhibits G = i^*F as an essential-image witness. Step 1
   carries both the equivalence and the canonical-unit assertion back to ci and cj. -/
theorem proEtaleRingModule_closed_essImage_iff_and_unit_isIso
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (Ri : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (Rj : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (ci : (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R ≅ Ri)
    (cj : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ Rj)
    (F : proEtaleRingModules X R) :
    ((proEtaleRingModuleDirectImage i R Ri ci).essImage F ↔
      IsZero ((proEtaleRingModulePullback j R Rj cj).obj F)) ∧
    (IsZero ((proEtaleRingModulePullback j R Rj cj).obj F) →
      IsIso ((proEtaleRingModuleAdjunction i R Ri ci).unit.app F)) := by
  sorry

end AlgebraicGeometry.Scheme
