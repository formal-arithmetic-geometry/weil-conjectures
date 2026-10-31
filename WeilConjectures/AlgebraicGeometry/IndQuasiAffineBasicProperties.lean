/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Defs.Filter
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import WeilConjectures.AlgebraicGeometry.IndQuasiAffinePermanence
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Basic properties of ind-quasi-affine schemes and morphisms

Source: Stacks Project, More on Morphisms, Tags 0AP6, 0F1U and 0AP7,
`definition-ind-quasi-affine`, `lemma-ind-quasi-affine-alternative-definition`,
and `lemma-base-change-ind-quasi-affine`
(blueprint: lem-sfb-ind-quasi-affine-base-change).

The scheme condition is written explicitly using Mathlib's `Scheme.IsQuasiAffine`.
For morphisms we reuse `indQuasiAffineProperty`: its quasi-compact opens map to an
*affine* target open, so quasi-affineness of those morphisms is equivalent to
quasi-affineness of their sources. This is Stacks Tag 0F1U, (1) iff (2).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Ind-quasi-affine schemes are separated and quasi-separated; ind-quasi-affine morphisms
are preserved by arbitrary base change and are local on the target for arbitrary open covers.

Source: Stacks Project, More on Morphisms, Tag 0AP6, definition and separation paragraph;
Tag 0F1U, final assertion; Tag 0AP7, base-change lemma.
(blueprint: lem-sfb-ind-quasi-affine-base-change).

Here the scheme hypothesis says that every quasi-compact open is quasi-affine, namely
isomorphic to a quasi-compact open of an affine scheme. `QuasiSeparatedSpace X` says that
the intersection of any two quasi-compact opens is quasi-compact. No compactness of X,
no affine condition on members of the target cover, and no nonemptiness are assumed.

Proof plan, following the node:
1. For affine opens A and B in X, their union W is quasi-compact and thus quasi-affine.
   By lem-trf-quasi-affine-canonical-affine-embedding it is separated. On A times B the
   diagonal of X is the pullback of the diagonal of W, by lem-weil-pbc-open-fibre-product.
   It is a closed immersion by lem-weil-pbc-closed-immersion-base-change. The affine-cover
   criterion lem-weil-pbc-closed-immersion-affine-cover-criterion makes X separated.
2. Cover two quasi-compact opens by finitely many affine opens. Every pairwise intersection
   is affine by lem-weil-pbc-separated-affine-open-intersection, hence quasi-compact.
   Their finite union is the desired intersection. Empty opens use empty finite covers.
3. Open subschemes inherit the ind-quasi-affine condition. A quasi-compact open of a
   quasi-affine scheme is quasi-affine by composing its open embedding into an affine.
4. Restrictions to target opens preserve the condition. Conversely, refine the given
   target cover by affine opens. For an affine target open B and a quasi-compact open K
   in its inverse image, K to B is quasi-compact by lem-weil-pbc-qcqs-morphism-permanence.
   Restricting to affine opens C of B subordinate to the refinement gives quasi-compact
   opens in the locally ind-quasi-affine sources. They are quasi-affine by hypothesis.
   Apply lem-sfb-quasi-affine-affine-cover-criterion to K to B and then
   def-nagata-quasi-affine-morphism to obtain quasi-affineness of K.
5. An affine morphism to an ind-quasi-affine scheme has ind-quasi-affine source:
   the image of a quasi-compact open lies in a finite union W of affine target opens.
   This W is quasi-affine. Its inverse image is quasi-affine by
   lem-sfb-affine-quasi-affine-affinization-square; apply step 3 to the original open.
6. For arbitrary base change, work over affine opens C in the new base contained in
   inverse images of affine opens B in the old base. By lem-weil-pbc-open-fibre-product,
   the restricted source is f inverse B times_B C. Its projection to f inverse B is
   affine, since its pullback to any affine open A is the affine A times_B C, by
   lem-weil-pbc-fibre-product-affine-spectra. Steps 5 and 3 make this restricted
   morphism ind-quasi-affine, and step 4 gives the result globally.
-/
theorem indQuasiAffine_basic_properties :
    (∀ X : Scheme.{u},
      (∀ U : X.Opens, IsCompact (U : Set X) → U.toScheme.IsQuasiAffine) →
        X.IsSeparated ∧ QuasiSeparatedSpace X) ∧
    (∀ (Y S T : Scheme.{u}) (f : Y ⟶ S) (g : T ⟶ S),
      indQuasiAffineProperty f → indQuasiAffineProperty (pullback.snd f g)) ∧
    (∀ (Y S : Scheme.{u}) (f : Y ⟶ S) (I : Type v) (U : I → S.Opens),
      iSup U = ⊤ →
        (indQuasiAffineProperty f ↔ ∀ i : I, indQuasiAffineProperty (f ∣_ U i))) := by
  sorry

end AlgebraicGeometry
