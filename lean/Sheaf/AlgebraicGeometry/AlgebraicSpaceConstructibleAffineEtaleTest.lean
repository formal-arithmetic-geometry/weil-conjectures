/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.Constructible
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import WeilConjectures.Topology.ConstructibleInConstructible
import WeilConjectures.Topology.ConstructibleIntersection
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Spectral.Basic

/-! # Affine étale tests for constructible subsets of algebraic spaces

Source: Stacks Project, Decent Spaces, Tag 0ECZ, the quasi-compact reduction;
Properties of Spaces, Tags 0ECT(2) and 0ECU
(blueprint: lem-sfb-space-constructible-affine-etale-test).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A subset of a quasi-compact, absolutely quasi-separated algebraic space is constructible
if and only if its preimage on every affine representable étale scheme chart is constructible.
Source: Stacks Project, Decent Spaces, Tag 0ECZ (proof in the quasi-compact case), and
Properties of Spaces, Tags 0ECT(2), 0ECU
(blueprint: lem-sfb-space-constructible-affine-etale-test).

Proof:
1. For a quasi-compact map to `X` and a quasi-compact open `W`, take an affine surjective
étale atlas of `W` (lem-sfb-qc-space-affine-etale-atlas). The pullback is quasi-compact.
The point fibre-product image formula (lem-a1-space-point-open-calculus) identifies its
image with the inverse image of `W`, which is quasi-compact by
lem-weil-pbc-continuous-image-quasi-compact and lem-a1-space-etale-open-image.
2. An affine chart is qcqs (lem-weil-pbc-affine-scheme-qcqs), and its map to the
quasi-separated target is quasi-compact (lem-sfb-space-qcqs-permanence). Both point spaces
are spectral by lem-weil-pbc-qcqs-scheme-spectral and lem-sfb-qcqs-space-spectral.
Retrocompact opens are quasi-compact opens
(lem-weil-pbc-spectral-open-retrocompact-iff-quasi-compact); step 1 and continuity give
constructibility of the preimage by lem-weil-pbc-constructible-preimage.
3. For the converse, change base to the integers (lem-sfb-space-change-base-to-integers)
and use lem-sfb-qcqs-space-splitting-filtration: finitely many quasi-compact opens `U_p`
have separated quasi-compact scheme covers `V_p` that are isomorphisms over the reduced
strata `T_p = U_p \ U_{p+1}`. The change of base preserves charts and point topology.
Open inclusions are étale (lem-weil-pbc-open-immersion-etale), and composition preserves
representable étaleness (lem-trf-space-representable-etale-scheme-tests), so every affine
open in `V_p` gives an allowed test.
4. The preimage `E_p` in `V_p` is locally constructible by these tests. It is constructible
by lem-trf-locally-constructible-qcqs-global, since separated implies quasi-separated
(lem-pc-separated-quasi-separated). The point space of `V_p` is spectral and its map to
`X` is quasi-compact by the scheme spectral lemma and lem-sfb-space-qcqs-permanence.
5. The inverse image of `U_{p+1}` in `V_p` is a quasi-compact open by step 1, hence is
retrocompact. Its complement `Z_p` is constructible. By
lem-weil-pbc-constructible-intersection-in-constructible, `E_p` restricts constructibly
to `Z_p`. The closed-support comparison (lem-sfb-space-reduced-closed-support), the
filtration isomorphism, and lem-a1-space-point-open-calculus identify `Z_p` homeomorphically
with `|T_p|`. Transport gives `E ∩ |T_p|` constructible in `|T_p|`.
6. Each `|T_p|` is a difference of quasi-compact, hence retrocompact, opens in the spectral
space `|X|`, so is constructible. Apply lem-weil-pbc-constructible-in-retrocompact-open
to obtain ambient constructibility of `E ∩ |T_p|`. Their finite union is `E`.
Empty strata and the empty space satisfy the same argument. -/
theorem isConstructible_iff_affine_etale_test {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X)
    (E : Set (Point X.obj.obj)) :
    Topology.IsConstructible E ↔
      ∀ (U : Over S) (a : yoneda.obj U ⟶ X.obj.obj),
        IsAffine U.left → IsEtale a → Topology.IsConstructible (schemePointMap a ⁻¹' E) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
