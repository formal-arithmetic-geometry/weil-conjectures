/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.AlgebraicGeometry.SchemeGroupoidLaws
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Ring.Subring.Basic
import Sheaf.AlgebraicGeometry.AffineGroupoidIntegralInvariants
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.CategoryTheory.Limits.MorphismProperty
import WeilConjectures.RingTheory.EtaleSectionIdempotentSplitting
import WeilConjectures.Algebra.Category.ModuleCat.FilteredColimitFlat
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.HenselianPairPrimeConnected
import WeilConjectures.RingTheory.IntegralOverHenselianPair
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Gluing
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.RingTheory.StrictHenselizationTriples

/-!
# Etale comparison of invariant spectra of affine groupoids

Source: Stacks Project, Groupoids, Tag 0DT9, `lemma-etale`
(blueprint: lem-sfb-affine-groupoid-etale-invariant-comparison).

The invariant rings are Mathlib's `RingHom.eqLocus` on global sections. The induced
ring map is specified by its composite with the inclusion of the primed invariant
subring. Thus the existential conclusion specifies the canonical restriction of
`a.appTop`, uniquely, rather than choosing an unspecified comparison map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A cartesian, stabilizer-preserving etale map of finite locally free affine groupoids
induces an etale map of invariant spectra and a cartesian quotient square.
Source: Stacks Project, `groupoids.tex`, Tag 0DT9, `lemma-etale`
(blueprint: lem-sfb-affine-groupoid-etale-invariant-comparison).

The base maps are `π` and `π'`; the arrow structure maps are `s ≫ π` and `s' ≫ π'`.
The groupoid laws imply that identity, inverse and composition are over the base
once source and target are. The identities for `a,b` include composition on every
test scheme, using the two projections to specify its induced pullback map.
The stabilizer square is expressed by its functor of points: every loop at `x ≫ a`
has a unique lift that is a loop at `x`. All scheme tests are used, including
nonreduced ones. This is precisely cartesianness of the scheme-theoretic stabilizers,
not merely a condition on geometric points.

The first conjunct characterizes the induced map on invariant functions. The last
conjunct says that the natural map from `U'` to the indicated fibre product is an
isomorphism, via the universal property of the chosen pullback. No nonemptiness,
positive rank, constant rank, or Noetherian hypothesis is imposed.

Proof (the eight steps of the DAG node):
1. Write the four affine schemes as spectra of A, B, A', B', and the invariant
   spectra as M and M'. Apply lem-weil-pbc-flat-tensor-exact to the equalizer
   sequences C → A → B and C' → A' → B'. Invariants commute with flat C-base
   change. Finite local freeness, etaleness, the three cartesian squares and all
   groupoid identities survive this base change, by fibre-product universality
   and lem-weil-pbc-etale-base-change-finite-limits.
2. Over strictly henselian local C, fix p' over the closed point. Apply
   lem-sfb-groupoid-strict-local-reduced-orbit: with J = radical(m A) and J' the
   radical ideal of its closed primed orbit, A/J → A'/J' is an isomorphism.
   The orbit points correspond bijectively, with identical residue fields.
3. By lem-a1-affine-groupoid-integral-invariants, A is integral over C. The node
   lem-weil-pbc-integral-over-henselian-pair makes (A,m A) henselian. Apply
   lem-sfb-henselian-pair-radical-etale-section to lift the inverse reduced map
   to an A-algebra retraction A' → A. Then
   lem-weil-pbc-etale-section-idempotent-splitting gives A' = A × A'' and a
   clopen W ≅ U containing precisely the selected closed orbit in that fibre.
4. The source preimage of W is finite over A, hence integral over C by
   lem-weil-pbc-finite-algebra-is-integral and lem-weil-pbc-integral-transitive.
   Apply lem-weil-pbc-integral-over-henselian-pair and
   lem-weil-pbc-henselian-pair-prime-connected: every point specializes to
   the closed fibre. Its specialized target is in the selected orbit in W;
   since W is clopen, the original target is in W. Inversion gives equality
   of source and target preimages. The source square identifies this arrow
   component with R. Thus the groupoid splits, and C' = C × C''; p' is in
   the first factor because its orbit is nonempty and lies in W.
5. For arbitrary p' over p, take the strict henselization H at a separable
   closure of κ(p), using lem-weil-pbc-strict-henselization-triples. It is a
   small filtered colimit of pointed etale C-algebras C_i. These are flat by
   lem-weil-pbc-etale-algebra-flat; their colimit is flat by
   lem-pc-filtered-colimit-commrings-elementwise and
   lem-weil-pbc-filtered-colimit-flat-modules. A point over p' and the closed
   point of Spec H exists since the residue-field tensor product is nonzero.
   Steps 1–4 give the invariant clopen section W_H ≅ U_H through that orbit.
6. The tensor-pushout universal property identifies A ⊗ H as the filtered
   colimit of A ⊗ C_i (lem-weil-pbc-algebra-tensor-pushout-universal-property).
   By lem-weil-pbc-etale-algebra-finite-presentation-localization and
   lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit, descend
   the A-algebra retraction to a stage. Its idempotent gives W_i ≅ U_i by
   lem-weil-pbc-etale-section-idempotent-splitting. Its two arrow images
   coincide at H and hence at a later stage by
   lem-pc-filtered-colimit-commrings-elementwise, applied also to B' ⊗ H.
   The descended idempotent is the original section's idempotent after base
   change. Thus C' ⊗ C_i = C_i × D_i, with Spec C_i a clopen neighbourhood
   of the chosen point, etale both over M' and over M.
7. Choose these charts at every p'. By lem-weil-pbc-scheme-coproduct-family,
   lem-weil-pbc-etale-local-on-source, and
   lem-trf-etale-descent-through-source-cover, M' → M is etale. The natural
   comparison U' → U ×_M M' is then etale by base change and cancellation
   (lem-weil-pbc-etale-base-change-finite-limits and
   lem-weil-pbc-etale-composition-cancellation).
8. For an algebraically closed field Ω and an Ω-point (u,y) of U ×_M M',
   pass to the strict henselization at the separable closure inside Ω.
   The reduced-orbit lemma identifies the orbit above y with the closed
   unprimed fibre, with identical residue fields. These fields are algebraic
   over the separably closed residue field, by
   lem-a1-affine-groupoid-integral-invariants and
   lem-a1-integral-residue-extension-algebraic. Each finite subextension has
   a unique embedding into Ω by
   lem-weil-pbc-sepclosed-finite-extension-unique-embedding; these agree on
   composita, giving a unique embedding of the whole residue field. Thus
   the comparison is bijective on Ω-points, compatibly with y. Passing to
   algebraic closures also shows injectivity on all field-valued points;
   def-weil-radicial-morphism makes it universally injective. It is
   surjective on points by geometric-point existence. The node
   lem-weil-pbc-radicial-etale-open makes it an open immersion, hence an
   isomorphism. The empty case is vacuous and no rank restriction was used. -/
theorem affineGroupoid_etale_invariant_comparison
    (S U R U' R' : Scheme.{u})
    (π : U ⟶ S) (π' : U' ⟶ S)
    (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R)
    (s' t' : R' ⟶ U') (e' : U' ⟶ R') (i' : R' ⟶ R')
    (c' : pullback s' t' ⟶ R')
    (_hG : Scheme.IsGroupoid s t e i c) (_hG' : Scheme.IsGroupoid s' t' e' i' c')
    (_hS : s ≫ π = t ≫ π) (_hS' : s' ≫ π' = t' ≫ π')
    (a : U' ⟶ U) (b : R' ⟶ R) (_ha : a ≫ π = π')
    (_he : e' ≫ b = a ≫ e) (_hi : i' ≫ b = b ≫ i)
    (_hc : ∀ (H : Scheme.{u}) (p' : H ⟶ pullback s' t') (p : H ⟶ pullback s t),
      p' ≫ pullback.fst s' t' ≫ b = p ≫ pullback.fst s t →
      p' ≫ pullback.snd s' t' ≫ b = p ≫ pullback.snd s t → p' ≫ c' ≫ b = p ≫ c)
    [IsAffine U] [IsAffine R] [IsAffine U'] [IsAffine R']
    [s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree]
    [s'.IsFiniteLocallyFree] [t'.IsFiniteLocallyFree] [Etale a]
    (_hs : IsPullback b s' s a) (_ht : IsPullback b t' t a)
    (_hstab : ∀ (H : Scheme.{u}) (x : H ⟶ U') (r : H ⟶ R),
      r ≫ s = x ≫ a → r ≫ t = x ≫ a →
      ∃! r' : H ⟶ R', r' ≫ b = r ∧ r' ≫ s' = x ∧ r' ≫ t' = x) :
    ∃ φ : s.appTop.hom.eqLocus t.appTop.hom →+* s'.appTop.hom.eqLocus t'.appTop.hom,
      (s'.appTop.hom.eqLocus t'.appTop.hom).subtype.comp φ =
        a.appTop.hom.comp (s.appTop.hom.eqLocus t.appTop.hom).subtype ∧
      Etale (Spec.map (CommRingCat.ofHom φ)) ∧
      IsPullback a
        (U'.toSpecΓ ≫ Spec.map
          (CommRingCat.ofHom (s'.appTop.hom.eqLocus t'.appTop.hom).subtype))
        (U.toSpecΓ ≫ Spec.map
          (CommRingCat.ofHom (s.appTop.hom.eqLocus t.appTop.hom).subtype))
        (Spec.map (CommRingCat.ofHom φ)) := by
  sorry

end AlgebraicGeometry
