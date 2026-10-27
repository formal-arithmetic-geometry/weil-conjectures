/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.SpaceSeparatedEtaleDiagonalComplement
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQcOpenSchematicClosure
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Limits

/-! # Integral surjective scheme covers of qcqs algebraic spaces

Source: Stacks Project, Decent Algebraic Spaces, Tag 09YB(1)
(blueprint: lem-sfb-qcqs-space-integral-scheme-cover).

Quasi-compactness is compactness of the field-valued point space. Quasi-separatedness
is absolute, expressed by the existing affine-test criterion. Integrality is tested on
all scheme base changes; surjectivity is equality of the point image with the whole space.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every quasi-compact and absolutely quasi-separated algebraic space has a surjective
integral cover by a scheme over its specified base.
Source: Stacks Project, Decent Algebraic Spaces, Tag 09YB(1)
(blueprint: lem-sfb-qcqs-space-integral-scheme-cover).

Proof, following the ten steps of the node and the proof of Tag 09YB(2):
1. Use lem-a1-space-etale-open-image and lem-trf-space-qc-finite-affine-atlas-refinement
   to choose a surjective etale affine scheme atlas U. The geometric fibres have a finite
   bound d by lem-sfb-space-qc-etale-fibre-bound. Prove the stronger induction assertion
   for any quasi-compact scheme U separated over Spec Z with this bound: the integral
   scheme cover locally factors through U. The atlas map is quasi-compact by
   lem-sfb-space-integral-qcqs-permanence and separated since its diagonal is the pullback
   of the closed absolute diagonal of U. Affine schemes are separated by
   lem-weil-pbc-affine-morphism-permanence.
2. Use strong induction on d. For empty X use the empty scheme; d = 0 forces this case.
   If d = 1, lem-sfb-space-separated-etale-diagonal-complement identifies the atlas with
   X; take U itself. Isomorphisms are integral by def-weil-finite-integral-morphism.
3. By lem-sfb-space-quasifinite-integral-compactification factor U through an open
   immersion into an integral B over X. Replace B by the schematic closure of U using
   lem-sfb-space-qc-open-schematic-closure. Closed immersions are integral by
   lem-weil-pbc-closed-immersion-integral-separated-uc. Integrality composes on scheme
   tests; B is qcqs by lem-sfb-space-integral-qcqs-permanence and U is dense in B.
4. The fibre product P = U x_X B is a quasi-compact separated scheme, since it is integral
   over U, by lem-sfb-space-integral-qcqs-permanence. Its projection to B is surjective
   etale by lem-trf-space-fibre-products-etale-covers. The section from U is closed by
   the diagonal of the integral B over X, and etale by
   lem-trf-space-chartwise-etale-permanence. A section is monic, so
   lem-sfb-space-etale-monomorphism-open makes it open. Thus P is U disjoint union W,
   where W is a quasi-compact separated scheme.
5. Let V be the open image of W in B, using lem-a1-space-etale-open-image. It is qcqs by
   lem-sfb-space-integral-qcqs-permanence. It contains B minus U. On U the fibres of W
   have at most d - 1 points, since the section accounts for one point of P; on all B
   they have at most d, by base change of the atlas.
6. The map W to B is separated etale and quasi-compact. By
   lem-sfb-space-etale-closed-degree-loci, the locus with at most d - 1 points is closed.
   It contains dense U, hence is all B. Induction on W to V gives a scheme Z integral
   and surjective over V, locally factoring through W.
7. The inclusion V into B is quasi-compact by lem-sfb-space-integral-qcqs-permanence.
   Extend Z to an integral E over B by lem-sfb-space-integral-extension-qc-open. Its
   restriction over V is Z. The inclusion of Z into E is quasi-compact by the same
   permanence lemma. Replace E by the schematic closure of Z using
   lem-sfb-space-qc-open-schematic-closure; the restriction over V stays Z and the map
   to B stays integral by lem-weil-pbc-closed-immersion-integral-separated-uc.
8. The opens Z and E x_B U cover E. Both are schemes, the second by integrality over U
   and lem-sfb-space-integral-qcqs-permanence. Thus lem-pc-schemes-criterion makes E a
   scheme. On the second open its map to X factors through U by projection; on Z use
   induction and W contained in U x_X B. The fibre-product identities give the claimed
   local factorizations over X.
9. By lem-sfb-space-reduced-closed-support take the reduced closed subspace T supported
   on B minus V. It lies in U and is therefore a closed subscheme of U. Form the scheme
   H = E disjoint union T by lem-weil-pbc-scheme-coproduct-family. Its map to B is
   integral: on affine tests the finite disjoint union is affine by
   lem-weil-pbc-affine-morphism-permanence, and the product of monic annihilating
   polynomials for two coordinates annihilates the pair. Compose with B to X using
   scheme-test integral composition.
10. The image of E contains V, and T covers B minus V; hence H surjects onto B. The
    image of B in X contains the surjective atlas image. Therefore H surjects onto X.
    The local factorizations on E and T complete the induction. Apply it to the affine
    atlas from step 1. Every construction and morphism is over S. -/
theorem exists_surjective_integral_scheme_cover {S : Scheme.{u}} (X : AlgebraicSpace S)
    [CompactSpace (Point X.obj.obj)] (hqs : IsAbsolutelyQuasiSeparated X) :
    ∃ (Y : Over S) (p : schemeSpace Y ⟶ X),
      IsRepresentableWith (fun _ _ q ↦ IsIntegralHom q.left) p.hom.hom ∧
        pointImage p.hom.hom = Set.univ := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
