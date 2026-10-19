/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Sheaf.AlgebraicGeometry.FpqcDescendingTypesMorphisms
import Sheaf.AlgebraicGeometry.AffineFpqcDescent
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import WeilConjectures.AlgebraicGeometry.InvariantOpenEffectiveDescent
import Sheaf.AlgebraicGeometry.FpqcInvariantIntersectionNeighbourhoods
import Sheaf.AlgebraicGeometry.IndQuasiAffinePermanence
import Sheaf.AlgebraicGeometry.IntersectionCanonicalAffineEmbedding
import Sheaf.AlgebraicGeometry.IntersectionSectionsFlatBaseChange

/-!
# Effective fpqc descent for ind-quasi-affine morphisms

Source: Stacks Project, More on Groupoids in Spaces, Tag 0APK, lemma-ind-quasi-affine,
specialized to a singleton fpqc covering; More on Morphisms, Tag 0F1U, condition (2)
(blueprint: lem-a1-ind-quasi-affine-fpqc-effective-descent).
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Over.DescentDatum

/-- A descent datum over a singleton fpqc covering is effective if every quasi-compact
open in the inverse image of every affine open of the base is quasi-affine over that open.
No quasi-compactness or local finite-presentation assumption on `V.hom` is required.

Source: Stacks Project, More on Groupoids in Spaces, Tag 0APK, lemma-ind-quasi-affine;
More on Morphisms, Tag 0F1U, condition (2).
(blueprint: lem-a1-ind-quasi-affine-fpqc-effective-descent)

`D.IsEffective` supplies a scheme over `B` whose pullback is `V`, with the pullback
identification compatible with the given datum, not merely an underlying scheme isomorphism.

Proof:
1. Let P be the condition in hV. By lem-a1-ind-quasi-affine-permanence it is stable under
   arbitrary base change and local on the target. It is stable under finite disjoint unions:
   check on affine opens in each target component, using lem-weil-pbc-scheme-coproduct-family.
   The empty coproduct case is vacuous. Apply lem-galois-fpqc-descending-types-morphisms to
   reduce to a flat surjection X -> S between affines.
2. Write S = Spec R and X = Spec A. The permanence lemma makes V ind-quasi-affine and
   quasi-separated. The cover is fpqc since a map between affines is affine, by
   lem-weil-pbc-morphism-affine-schemes-affine. At each v in V use
   lem-a1-fpqc-invariant-intersection-neighbourhoods to choose v in W contained in E,
   where W is invariant open and E is an invariant intersection of a nonempty family of
   quasi-compact opens. No openness or scheme structure on E is assumed.
3. Put C = Gamma(E, O_V restricted to E). The datum restricts to the two inverse images
   E_0 and E_1. By lem-a1-intersection-sections-flat-base-change their section rings are
   C tensor_R A and A tensor_R C. Its comorphism gives the algebra isomorphism psi from
   A tensor_R C to C tensor_R A. Apply the same lemma after another flat base change,
   using lem-weil-pbc-flat-morphism-base-change. Its naturality and iterated compatibility
   turn the geometric cocycle into psi_02 = psi_01 composed with psi_12; taking sections
   reverses composition. This verifies the omitted cocycle without making E a scheme.
4. Let Z = Spec C over X. By lem-weil-pbc-fibre-product-affine-spectra and
   def-weil-affine-spectrum, Spec psi defines the descent isomorphism on Z and the algebra
   cocycle gives its geometric cocycle. The structure morphism is affine by
   lem-weil-pbc-morphism-affine-schemes-affine. Apply lem-galois-fpqc-affine-descent-effective
   to obtain Z_0 over S and a datum-compatible pullback identification with Z.
5. By lem-a1-intersection-canonical-affine-embedding the canonical map j_E identifies W
   with an open J in Z. Check its base-change comparison on affine opens L in W: writing
   D_L = Gamma(L, O_L), its map to Z corresponds to restriction C -> D_L by
   lem-weil-pbc-morphism-into-affine-scheme. The tensor square identifies its base change
   by lem-weil-pbc-fibre-product-affine-spectra. Naturality of
   lem-a1-intersection-sections-flat-base-change sends c tensor a to its restriction
   tensor a, so the canonical maps agree. These local comparisons glue. Since psi is the
   comorphism of the original datum on E_0, Spec psi carries the full inverse image of J
   onto its other inverse image. Under Z = Z_0 times_S X these are the two inverse images
   of J in Z times_{Z_0} Z.
6. By lem-galois-fpqc-covering-base-change, Z -> Z_0 is fpqc. Thus
   lem-weil-pbc-open-subscheme-fpqc-descent descends J to an open W_0 in Z_0. Its pullback
   is W, compatibly with the restricted datum: the canonical embedding intertwines the
   datum by the restriction calculation in step 5. Hence the datum on W is effective.
7. The W obtained for every v cover V and their inclusions respect the restricted data.
   By lem-pd-effective-invariant-open-cover their effective models glue. This proves the
   affine case in step 1 and hence the original singleton-cover assertion. No step used
   quasi-compactness or local finite presentation of V -> A. When V is empty, the empty
   invariant open cover gives the empty scheme over B. -/
theorem isEffective_of_indQuasiAffine_fpqc {A B : Scheme.{u}} (p : A ⟶ B)
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage B) {V : Over A}
    (hV : ∀ (U : A.Opens), IsAffineOpen U →
      ∀ (K : (Limits.pullback V.hom U.ι).Opens),
        IsCompact (K : Set (Limits.pullback (C := Scheme.{u}) V.hom U.ι)) →
          IsQuasiAffineHom (K.ι ≫ Limits.pullback.snd V.hom U.ι))
    (D : Over.DescentDatum p V) : D.IsEffective := by
  sorry

end CategoryTheory.Over.DescentDatum
