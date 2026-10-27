/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q157
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Sheaf.AlgebraicGeometry.SeparatedEtaleChart
import Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.UniversallyHomeomorphIntegral
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Separated universal homeomorphisms of algebraic spaces are integral

Source: Rydh, Submersions and effective descent of étale morphisms, Corollary (5.22),
printed pp.24–25, and Appendix B, printed p.38
(blueprint: lem-sfb-separated-space-homeomorphism-affine).

The hypothesis quantifies over all algebraic-space base changes. The conclusion uses
scheme-test representability with the integral-morphism property, which includes
affineness and integrality of the maps on rings over every affine open.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated universal homeomorphism of algebraic spaces is representable by schemes
and integral. In particular, every scheme base change is affine, and over any affine
open its coordinate algebra is integral over the target coordinate ring.
Source: Rydh, Corollary (5.22), printed pp.24–25, and Appendix B, printed p.38
(blueprint: lem-sfb-separated-space-homeomorphism-affine).

Proof:
1. For a scheme test T → Y, form Z = X ×_Y T. Fibre-product associativity preserves
   universal homeomorphy, and separatedness is preserved by base change
   (lem-trf-space-fibre-products-etale-covers, lem-sfb-space-separated-fp-composition).
   First take T affine. Its point space, hence that of Z, is quasi-compact; choose an
   affine étale scheme atlas U' → Z (lem-weil-pbc-affine-scheme-qcqs,
   lem-sfb-qc-space-affine-etale-atlas).
2. Affine schemes are absolutely separated and quasi-separated. The closed diagonal of T
   remains closed after scheme tests. Separated composition makes Z absolutely separated;
   its closed diagonal is proper and quasi-compact, hence Z is quasi-separated
   (lem-weil-pbc-affine-source-morphism-separated,
   lem-weil-pbc-closed-immersion-base-change, lem-sfb-space-closed-subspace-proper).
   The atlas U' → Z is separated by lem-a1-separated-etale-chart.
3. Descend U' along Z → T by lem-sfb-homeomorphism-separated-etale-equivalence, obtaining
   a separated étale space U → T with U ×_T Z ≅ U'. By lem-a1-separated-etale-space-scheme,
   U is a scheme. Point surjectivity of U' → Z, the homeomorphism |Z| → |T|, and the
   factorization through U show that U → T is surjective (lem-a1-space-point-open-calculus).
4. The scheme map U' → U is a universal homeomorphism, hence integral and affine by
   lem-trf-universally-homeomorph-integral and def-weil-finite-integral-morphism.
   Descend affineness along U → T using lem-sfb-space-affine-locality: Z is an affine
   scheme, and its scheme universal homeomorphism to T is integral by the same lemma.
5. For arbitrary T, these affine-test schemes agree over overlaps by their fibre-product
   projections. Glue using lem-weil-pbc-relative-glueing-affine-opens. Maps and sections
   glue uniquely by def-trf-algebraic-space and lem-weil-pbc-scheme-morphism-gluing, so
   the glued scheme represents X ×_Y T. By pqf-lem-affine-local-target its projection
   is affine. It is a scheme universal homeomorphism, hence integral. Finally,
   def-weil-finite-integral-morphism gives the monic-polynomial description on affine opens.
No quasi-separatedness assumption on X, Y, or S is needed: step 2 supplies the
quasi-separated spaces to which Rydh's global convention applies. -/
theorem isRepresentableWith_isIntegralHom_of_separated_universally_isHomeomorph
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (r : X ⟶ Y)
    (hsep : MapIsSeparated r)
    (hhome : ∀ (T : AlgebraicSpace S) (t : T ⟶ Y),
      IsHomeomorph (mapPoint (Limits.pullback.snd r.hom t.hom).hom)) :
    IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left) r.hom.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
