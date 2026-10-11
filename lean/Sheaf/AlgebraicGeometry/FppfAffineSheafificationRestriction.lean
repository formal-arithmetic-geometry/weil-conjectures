/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker J1
-/
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over

/-!
# Restriction of fppf sheafification to affine schemes

Source: Stacks Project, Topologies, Lemma 34.7.11 (Tag 021V)
(blueprint: lem-pc-fppf-affine-sheafification-restriction).
-/

universe u

open CategoryTheory CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

/-- (blueprint: lem-pc-fppf-affine-sheafification-restriction) For a scheme `S`, restriction
of the fppf sheafification of a presheaf on schemes over `S` to affine schemes over `S`
is naturally isomorphic to sheafification after restriction (Stacks, Tag 021V).

The affine fppf site is `CostructuredArrow Scheme.Spec S` with the coverings whose
underlying scheme morphisms form an fppf covering (`fppfPrecoverage.comap`), as in
`fppf_affine_site_topos_equivalence`.

Proof:
1. By `lem-pc-fppf-affine-site-topos-equivalence`, the inclusion is fully faithful, every
   scheme over `S` has an fppf covering by affine objects, and every fppf covering of an
   affine object is refined by a covering of the affine site; conversely a covering of the
   affine site is an fppf covering. So a sieve on an affine `U` covers in the affine site
   iff the sieve it generates on `u(U)` covers in the big site: the affine fppf topology is
   the topology induced by the inclusion, and restriction is an equivalence of sheaf
   categories.
2. These are the hypotheses of the dense-subsite sheafification compatibility
   (`lem-pc-dense-subsite-sheafification-compatibility`), which gives an isomorphism
   between affine-site sheafification of the restriction and the restriction of the
   big-site sheafification, natural in the presheaf. -/
theorem fppfSheafification_affineRestriction (S : Scheme.{u}) :
    Nonempty <| sheafification (fppfTopology.over S) (Type (u + 1)) ⋙
        (whiskeringLeft _ _ (Type (u + 1))).obj
          (CostructuredArrow.toOver Scheme.Spec S).op ≅
      (whiskeringLeft _ _ (Type (u + 1))).obj
          (CostructuredArrow.toOver Scheme.Spec S).op ⋙
        sheafification
          ((fppfPrecoverage.comap
            (CostructuredArrow.toOver Scheme.Spec S ⋙ Over.forget S)).toGrothendieck)
          (Type (u + 1)) := by
  sorry

end AlgebraicGeometry.Scheme
