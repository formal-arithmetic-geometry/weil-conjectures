/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# An almost dense finite locally free locus for a finite groupoid

Source: Stacks Project, More on Groupoids in Spaces, Tag 0ABA,
`lemma-finite-flat-over-almost-dense-subscheme`
(blueprint: lem-sfb-finite-groupoid-almost-dense-flat-locus).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A groupoid with finite source and target admits an invariant open and an invariant
closed thickening with finite locally free restricted source and target, whose open
has saturated closure equal to the whole object scheme.

Source: Stacks Project, Tag 0ABA, `lemma-finite-flat-over-almost-dense-subscheme`
(blueprint: lem-sfb-finite-groupoid-almost-dense-flat-locus).

The equality of open inverse images expresses invariance of `W` as an open subscheme.
The isomorphism between the two pullbacks of `j ≫ W.ι`, compatible with their maps
into `R`, expresses equality as subschemes, including their scheme structures.
The arrow scheme of the restriction is `(W' ×[U,s] R) ×[t,U] W'`.
Its source is the composite of the two first projections and its target is the
last projection, exactly as in the double restriction in the node.

Proof, following the eight steps of the node:
1. Use lem-sfb-finite-groupoid-invariant-rank-filtration to obtain invariant closed
   subschemes Z_n with empty intersection and finite locally free rank-r strata.
   Inductively construct disjoint invariant opens W_r and closed thickenings W'_r,
   maintaining U minus Z_n contained in the union of the saturated closures of W_r
   for 1 ≤ r ≤ n. The initial assertion follows from Z_0 = U.
2. Each saturated closure is invariant by lem-sfb-groupoid-subset-saturation-invariant
   and closed by continuity of s and the finite closed-map assertion of
   lem-weil-pbc-finite-closed-map-finite-fibres. Finite unions remain closed invariant.
3. Take W_(n+1) to be the complement of Z_(n+1) and the previous saturated closures.
   The induction puts it inside Z_n minus Z_(n+1). Invariance follows by taking
   inverse images, and the identity section puts each previous W_r inside its
   saturated closure, giving disjointness.
4. Set W'_(n+1) = Z_n ×_U W_(n+1). It is closed with full support and invariant
   scheme-theoretically. It is open in the rank-(n+1) stratum, so the restricted
   source is finite locally free of that degree, using
   lem-weil-pbc-finite-morphism-permanence and the affine-local definitions of
   flatness and local finite presentation. Inversion gives the same for target.
5. Adjoin the next saturated closure. A point outside Z_(n+1) is either already
   covered or lies in W_(n+1), hence in its saturated closure by the identity.
   This closes the induction, beginning with W_1 = W'_1 = U minus Z_1.
6. Take the union of the pairwise disjoint opens W_r. Glue their defining quotient
   ideal sheaves to obtain the closed immersion W' into W. Full support gives
   the homeomorphism. Equality of inverse-image subschemes glues on this cover,
   proving invariance of both W and W'.
7. For an invariant monomorphism, double restriction equals either single inverse
   image. Thus the global restricted source is finite by base change of s
   (lem-weil-pbc-finite-morphism-permanence). Flatness and local finite presentation
   hold on each disjoint piece and hence everywhere. This is finite local freeness
   (def-pc-finite-locally-free). Inversion gives the target assertion.
8. The empty intersection of the Z_n puts every point outside some Z_n, hence in
   a saturated closure of a W_r. Monotonicity of closure, inverse image and image
   then gives the saturated-closure equality for W. -/
theorem IsGroupoidScheme.exists_almostDense_finiteLocallyFree
    {U R : Scheme.{u}} (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s t ⟶ R) (hG : IsGroupoidScheme s t e i c)
    [IsFinite s] [IsFinite t] :
    ∃ (W : U.Opens) (W' : Scheme.{u}) (j : W' ⟶ W.toScheme),
      IsClosedImmersion j ∧
      s ⁻¹ᵁ W = t ⁻¹ᵁ W ∧
      (∃ E : pullback s (j ≫ W.ι) ≅ pullback t (j ≫ W.ι),
        E.hom ≫ pullback.fst t (j ≫ W.ι) = pullback.fst s (j ≫ W.ι)) ∧
      IsHomeomorph j ∧
      t '' (s ⁻¹' closure (W : Set U)) = Set.univ ∧
      (pullback.fst (pullback.snd (j ≫ W.ι) s ≫ t) (j ≫ W.ι) ≫
        pullback.fst (j ≫ W.ι) s).IsFiniteLocallyFree ∧
      (pullback.snd (pullback.snd (j ≫ W.ι) s ≫ t) (j ≫ W.ι)).IsFiniteLocallyFree := by
  sorry

end AlgebraicGeometry
