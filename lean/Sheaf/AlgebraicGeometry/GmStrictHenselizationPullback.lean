/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.Sites.Gm
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Pullback of the units sheaf to a strict henselization

Source: Stacks Project, Tag 03Q9, proof, and Tag 09YQ, continuity on inverse limits
(blueprint: lem-weil-pbc-gm-pullback-strict-henselization).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The canonical units comparison is invertible after base change to a strict henselization.
Source: Stacks Project, Tag 03Q9, proof, using Tag 09YQ
(blueprint: lem-weil-pbc-gm-pullback-strict-henselization).

Here `p = pullback.fst f ρ` is the projection `X ×_S S_(s) ⟶ X`, for the structural
morphism `ρ = strictHenselizationStructuralMap s : S_(s) ⟶ S`, and the comparison
`p⁻¹ 𝔾ₘ ⟶ 𝔾ₘ` is the adjoint of the pullback-of-units map `𝔾ₘ ⟶ p_* 𝔾ₘ`.

Proof, Step 1: `def-weil-pbc-strict-henselization-limit` gives the cofiltered affine
pointed-neighbourhood limit. Reindex by a nonempty directed set using
`lem-weil-pbc-cofiltered-limit-directed-reindex` and base change along `f`. Fibre products
commute with limits, so the resulting limit projection is `pullback.fst f ρ`.
`lem-weil-pbc-limit-affine-transition` gives affine transition maps;
`lem-weil-pbc-qcqs-morphism-permanence` gives qcqs stages and quasi-separated limit.

Step 2: For an affine étale test object on the limit, permanence makes its morphism
finitely presented. `lem-weil-pbc-etale-finite-data-descent` descends it to a qcqs étale
object at a stage. The stage maps to `X` are étale, so
`lem-weil-pbc-etale-inverse-image-restriction` identifies the restricted units sheaves.
`lem-weil-pbc-inverse-image-composition` and `lem-weil-pbc-etale-section-continuity`
identify inverse-image sections with the colimit of units on these descended objects.
`lem-weil-pbc-descend-affine` makes them affine eventually, since the test object and
strict henselization are affine. The affine clause of
`lem-weil-pbc-limit-affine-transition` identifies its coordinate ring with the directed
colimit of the stage rings. A unit and its inverse descend to one finite stage, and
their inverse equations hold at some later stage; hence units commute with this colimit.
These identifications send a stage unit to its pullback, so their composite is the
canonical adjoint comparison `upperStarGmSheafToGmSheaf`. It is bijective on affine étale
test objects. Those objects cover every étale object, and the sheaf axiom therefore
makes the comparison an isomorphism. -/
theorem isIso_upperStarGmSheafToGmSheaf_strictHenselization
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    IsIso (upperStarGmSheafToGmSheaf
      (pullback.fst f (strictHenselizationStructuralMap s))) := by
  sorry

end AlgebraicGeometry.Scheme
