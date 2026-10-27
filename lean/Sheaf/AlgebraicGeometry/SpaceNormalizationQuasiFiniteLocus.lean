/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated
import WeilConjectures.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs
import Sheaf.AlgebraicGeometry.SpaceInvariantOpenQuotient
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.SpaceOpenImmersionEtaleLocal

/-! # The quasi-finite locus in a relative normalization of algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tag 0ABR, with the normalization
characterization of Tag 0823 (blueprint: lem-sfb-space-normalization-quasifinite-locus).

The normalization is a fixed integral factorization with its universal property.
The quasi-finite locus is expressed by a lift to a representing scheme pullback over an
etale target chart. The inverse image of an open is the literal subfunctor preimage;
`Subfunctor.fromPreimage` is its canonical projection to that open.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The quasi-finite locus of a representable separated finite-type map is the full
inverse image of an open in its relative normalization, and its map onto that open is
an isomorphism. Scheme tests in `hf` express representability and local finite type
simultaneously. In the point predicate, `IsPullback` identifies `U` with `V ×_Y T`,
`q` is its projection to `V`, and `p` is its scheme projection to the etale target chart.
The open inverse-image structure is precisely the inclusion of the subfunctor preimage.
Source: Stacks Project, Morphisms of Spaces, Tags 0ABR and 0823
(blueprint: lem-sfb-space-normalization-quasifinite-locus).

Proof:
1. Choose a surjective etale scheme atlas T of Y (def-trf-algebraic-space), and form
   V_T and N_T (lem-trf-space-fibre-products-etale-covers). They are schemes by the
   representability hypotheses. The map f_T is separated and finite type. The theorem
   lem-sfb-space-integral-factorization-etale-base-change supplies the pulled-back
   universal property. Compare it to the concrete scheme normalization from
   lem-weil-pbc-relative-normalization using lem-sbc-relative-normalization-universal-property.
   The unique comparison maps in both directions are inverse and commute with both arrows.
2. Apply lem-sfb-scheme-normalization-isolated-fibre-open and transfer the resulting
   open to N_T. Identify its inverse image with the scheme quasi-finite locus Q_T by
   lem-weil-pbc-quasi-finite-at-point-isolated and
   lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs, using pqf-def-quasifinite.
3. The common refinement of two etale target charts and the compatible-point lifting
   in lem-a1-space-point-open-calculus identify the point predicate independently of
   the chosen lift, by lem-sfb-scheme-quasifinite-at-base-change. Its inverse image in
   V_T is Q_T. Atlas openness and surjectivity show the locus Q is open. Apply
   lem-a1-space-invariant-open-quotient to obtain an open U of V with point image Q.
   The point-open calculus identifies its pullback with the open from step 2.
4. By lem-trf-space-open-immersion-etale-local, U to N is an open immersion: its
   base change to N_T is the isomorphism of step 2 followed by the open inclusion.
   Its image subfunctor W is open and U to W is an isomorphism; its pullback to N_T
   is exactly the open of step 2 (def-a1-space-open-subspace).
5. The full inverse image of W has the same pullback to V_T as U. The surjective
   atlas therefore gives equal point subsets in V, and lem-a1-space-point-open-calculus
   gives equality of their open subfunctors. Thus the canonical map from the literal
   subfunctor preimage to W is the isomorphism already obtained, including its
   induced open structure. -/
theorem exists_openSubspace_normalization_quasiFinite_locus
    {S : Scheme.{u}} {V Y N : AlgebraicSpace S} (f : V ⟶ Y)
    (hf : IsRepresentableWith (fun _ _ p ↦ LocallyOfFiniteType p.left) f.hom.hom)
    (hsep : MapIsSeparated f) (hqc : MapIsQuasiCompact f.hom.hom)
    (g : V ⟶ N) (ν : N ⟶ Y) (hfactor : g ≫ ν = f)
    (hν : IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left) ν.hom.hom)
    (huniv : ∀ (Z : AlgebraicSpace S) (h : V ⟶ Z) (π : Z ⟶ Y),
      IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left) π.hom.hom →
      h ≫ π = f → ∃! c : N ⟶ Z, g ≫ c = h ∧ c ≫ π = ν) :
    ∃ W : OpenSubspace N,
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)
        (W.val.preimage g.hom.hom).ι ∧
      IsIso (W.val.fromPreimage g.hom.hom) ∧
      pointImage (W.val.preimage g.hom.hom).ι =
        {v : Point V.obj.obj | ∃ (T : Over S) (a : yoneda.obj T ⟶ Y.obj.obj),
          IsEtale a ∧ ∃ (U : Over S) (q : yoneda.obj U ⟶ V.obj.obj) (p : U ⟶ T),
            IsPullback q (yoneda.map p) f.hom.hom a ∧
            ∃ x : U.left, schemePointMap q x = v ∧ p.left.IsQuasiFiniteAtPoint x} := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
