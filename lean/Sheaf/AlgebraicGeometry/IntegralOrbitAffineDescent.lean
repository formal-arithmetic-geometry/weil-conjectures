/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q132
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget

/-!
# Invariant affine neighbourhoods descend along integral orbit covers

Source: Stacks Project, `more-groupoids.tex`, Tag 0ABE (lemma-find-affine-integral)
(blueprint: lem-sfb-integral-orbit-affine-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An invariant affine neighbourhood for an integral groupoid orbit cover descends from
the iterated pullback groupoid.

Source: Stacks Project, `more-groupoids.tex`, Tag 0ABE (lemma-find-affine-integral)
(blueprint: lem-sfb-integral-orbit-affine-descent).

Proof plan (Tag 0ABE, with its omitted pointwise details expanded):
1. By lem-weil-common-extension-fields-tensor-nontrivial, the tensor product of the
   residue fields of two points over a common image is nonzero. Choose a maximal ideal
   using lem-weil-common-extension-fields-maximal-ideal. Then
   lem-weil-pbc-fibre-product-points lifts these exact two points to the fibre product.
2. The identity, inverse and composition laws of def-a1-groupoid-scheme make the relation
   of being joined by an arrow an equivalence relation. For transitivity, use step 1 to
   lift composable underlying points. Two successive applications of step 1 show that
   two points of T are related precisely when their images in U are related. Thus V
   contains every restricted orbit which meets it.
3. Put P = T ×[a,U,t] R, with projections p to T and q to R, and h = q ≫ s.
   The maps p and q are integral by lem-sbc-integral-morphism-base-change. By the
   composition clause of lem-weil-pbc-closed-immersion-integral-separated-uc, h is
   integral. Since integral morphisms are affine, the open p⁻¹(V) is affine by
   pqf-def-affine-morphism.
4. Put W = h(p⁻¹(V)). Step 1 identifies membership in W with being related to a(v)
   for some v in V. By step 2 this set is invariant, and h⁻¹(W) = p⁻¹(V): if h(z)
   lies in W, the arrow q(z) relates h(z) to a(p(z)), so p(z) is related to some v
   in V and hence lies in V. The identity arrow shows a(x) belongs to W.
5. Every orbit meets a(T), so step 1 lifts an arrow from any u to some a(y) to P.
   Therefore h is surjective. By pqf-lem-integral-univclosed and the universally closed
   definition in def-weil-proper-morphism, h is closed. The complement of W is the image
   under h of the closed complement of p⁻¹(V). Thus W is open and defines an open
   subscheme as in def-pc-scheme.
6. The map p⁻¹(V) → W is the base change of h, hence integral and surjective.
   Its source is affine by step 3. Apply
   lem-weil-pbc-surjective-universally-closed-affine-target to see that W is affine.
   Invariance in step 4 gives equality of its source and target inverse-image opens.

The restricted arrow scheme is the displayed iterated pullback
`pullback (pullback.snd a s ≫ t) a`. Its source is the first projection followed by
`pullback.fst a s`, and its target is the second projection. Equality in `Scheme.Opens`
is equality of the corresponding canonical open subschemes. Only these endpoint maps
are needed to express the invariant-open hypothesis; no choices of operations are needed.
-/
theorem integral_orbit_affine_descent
    {U R T : Scheme.{u}} (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s t ⟶ R) (hG : IsGroupoidScheme s t e i c)
    [IsIntegralHom s] [IsIntegralHom t] (a : T ⟶ U) [IsIntegralHom a]
    (horbit : ∀ u : U, ∃ y : T, ∃ r : R, s r = u ∧ t r = a y)
    (x : T) (V : T.Opens) (hxV : x ∈ V) (hV : IsAffineOpen V)
    (hVinvar :
      (pullback.fst (pullback.snd a s ≫ t) a ≫ pullback.fst a s) ⁻¹ᵁ V =
        (pullback.snd (pullback.snd a s ≫ t) a) ⁻¹ᵁ V) :
    ∃ W : U.Opens, IsAffineOpen W ∧ a x ∈ W ∧ s ⁻¹ᵁ W = t ⁻¹ᵁ W := by
  sorry

end AlgebraicGeometry
