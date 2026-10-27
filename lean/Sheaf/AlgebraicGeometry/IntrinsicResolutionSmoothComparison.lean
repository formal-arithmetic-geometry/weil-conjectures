/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.IntrinsicLabeledResolution

/-!
# Smooth comparisons of embedded-compatible ordinary towers

Source: ILO VIII 2.1.9, 2.3.11--2.3.13, pp.88,93--94; Stacks 01V7 and 07CK.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Fixed ordinary towers agreeing with a synchronized embedded assignment admit
cartesian comparisons along every smooth rational morphism. These recover each
supplied comparison on a cartesian square of embedded pairs.

Source: ILO VIII 2.1.9, 2.3.11--2.3.13, pp.88,93--94, expanded by Steps 3--9 of
lem-trf-embedded-to-intrinsic-smooth-resolution using Stacks 01V7 and 07CK
(blueprint: lem-trf-intrinsic-resolution-smooth-comparison).

Proof: For an open U of an embedded input X in P, take O=P minus (X minus U).
Then U=X times_P O and O is again a permitted ambient: it is smooth, separated,
and finite type over Q, since P is Noetherian and O is quasi-compact. Apply E's
cartesian smooth comparison to O -> P and transport through a and b. Rigidity of
ordinary blowup towers makes these open comparisons independent of ambient opens
and embeddings, and compatible on nested opens.
Cover h by standard-smooth affine charts V -> U. Embed U in Spec R for a finite
polynomial Q-algebra R with quotient R/I its coordinate ring. Lift the standard
smooth algebra of V through R -> R/I by lifting its finite Jacobian presentation
and inverting the lifted determinant. This uses no nilpotence assumption on I.
The lifted spectrum Q is a smooth affine finite-type ambient over Spec R and over
Q, and V=U times_(Spec R) Q. Apply E's smooth comparison on this cartesian pair,
and transport by the given identifications and the open comparisons.
Index both finite towers by the union of their labels. Induct on this ordered
union. At the initial cut the comparison is h. At each next cut the inverse images
of the chart opens cover the current source level. The local comparisons identify
the actual source center ideal with the extended target ideal. Rigidity from the
blowup universal property identifies preceding chart maps, so these ideal equalities
are on the same scheme and glue. An ideal is unit exactly when it is unit on this
cover; hence precisely the unit stages disappear and no new label appears. Each
current projection is a smooth base change of h and therefore flat. Flat blowup
base change gives the next cartesian square; blowing up a unit ideal is the identity.
The finite induction gives a natural transformation, its cartesian squares, centers
and retained clauses. On a supplied cartesian smooth ambient square, the embedded
comparison has these same local ideals and maps, so blowup rigidity identifies it
with the constructed comparison. This is exactly the displayed compatibility
identity. Nothing requires separation of h, surjectivity, or constant relative
dimension. Empty towers and charts missing centers use the unit-ideal case. -/
theorem exists_intrinsic_smooth_comparison
    {L : Type w} [LinearOrder L] (E : SynchronizedEmbeddedResolution.{u, w} L)
    (S T : EmbeddableResolutionInput.{u})
    (A : IntrinsicLabeledOrdinaryTower L S.val.scheme)
    (B : IntrinsicLabeledOrdinaryTower L T.val.scheme)
    (a : ∀ p : RationalResolutionEmbedding S.val,
      IntrinsicEmbeddedResolutionIdentification A p (E.tower p.pair))
    (b : ∀ q : RationalResolutionEmbedding T.val,
      IntrinsicEmbeddedResolutionIdentification B q (E.tower q.pair))
    (h : T.val.scheme ⟶ S.val.scheme)
    (_over : h ≫ S.val.structureMap = T.val.structureMap) [Smooth h] :
    ∃ c : IntrinsicLabeledResolutionPullback h A B,
      ∀ (p : RationalResolutionEmbedding S.val) (q : RationalResolutionEmbedding T.val)
        (f : EmbeddedResolutionSmoothMap q.pair p.pair),
        q.iso.hom ≫ f.intrinsic = h ≫ p.iso.hom →
          c.map ≫ (a p).iso.hom = (b q).iso.hom ≫ (E.pullback f).intrinsic := by sorry

end AlgebraicGeometry
