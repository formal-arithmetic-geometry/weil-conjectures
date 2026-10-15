/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
import Sheaf.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

/-!
# The closed counit on abelian pro-etale sheaves

Source: Stacks Project, Tags 09AA, 09BL and 09BK
(blueprint: lem-weil-pbc-proetale-abelian-closed-counit).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Closed direct image on abelian pro-etale sheaves is fully faithful, expressed by the
invertibility of the actual inverse-image/direct-image adjunction counit.

Source: Stacks Project, Tags 09AA, 09BL and 09BK
(blueprint: lem-weil-pbc-proetale-abelian-closed-counit).

Proof:
1. Restrict to affine opens of X and their inverse images in Z. The direct-image formula
commutes with these open restrictions by base change. The inverse-image comparison follows
by adjunction, and carries the counit to the restricted counit. Thus it suffices to prove
invertibility when X and Z are affine, presenting i as Spec(A/I) → Spec A.
2. Replace the two pro-etale sites by their ind-etale affine bases. The cover-dense
restriction functors are equivalences on sheaves and commute with direct image. On the
bases let u be base change and v the closed-site lift. The affine closed-site functor
properties give v left adjoint to u, with invertible unit, and v cocontinuous and preserving
covering families. The opposite adjunction computes left Kan extension along u.op as
precomposition with v.op. Consequently inverse image is sheafification after that
precomposition. These comparisons are mates of the actual direct-image comparison, so
identify the actual adjunction counit.
3. For an abelian sheaf G on the closed basis, that presheaf for i* i_* G is
V ↦ G(u(v(V))). The invertible site unit V → u(v(V)) identifies it naturally with G.
This is already a sheaf; sheafification therefore changes it only by its canonical
isomorphism. Under these identifications the counit is the identity, so is invertible.
The comparison uses additive maps throughout and thus applies directly to abelian sheaves.
4. The affine counits agree on overlaps because all comparisons preserve the adjunction
counit. Local inverses glue, giving the assertion on arbitrary X. Neither reducedness of Z,
finite presentation of its ideal, nor a quasi-compact open complement is used. For empty Z
both sides are the unique zero sheaf, and the same calculation applies. -/
theorem abelian_closed_counit {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    IsIso (upperStarLowerStarAdjunction Ab.{u + 1} i).counit := by
  sorry

end AlgebraicGeometry.ProEtale
