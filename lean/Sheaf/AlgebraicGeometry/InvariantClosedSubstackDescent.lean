/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.ClosedModuliSubstack
public import Sheaf.AlgebraicGeometry.InvariantClosedAtlasIdeal

/-! # Invariant closed subschemes descend to closed substacks

Source: Stacks Project, stacks-properties.tex, Tags 0507 and 04YN
(blueprint: lem-sfb-invariant-closed-substack-descent).

The equivalence is characterized by the actual scheme 2-base change. Ideals encode
closed subschemes without replacing their scheme structure by point subsets.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- Pullback to a smooth surjective atlas bijects closed substacks with invariant closed
subschemes. Every corresponding closed scheme is a smooth surjective representable atlas
of its descended substack, and the latter is algebraic.
Source: Stacks Project, Tag 0507 (lemma-substacks-presentation), closed case, and Tag 04YN
(blueprint: lem-sfb-invariant-closed-substack-descent).

Proof:
1. A closed substack pulls back to a closed subscheme. Strict fullness makes its two
inverse images under the relation equal as subfunctors, hence as closed subspaces
(def-sfb-stable-pointed-moduli-groupoids).
2. By lem-sfb-etale-smooth-atlas-fppf-descent the ambient stack is an fppf stack. For an
invariant closed scheme Z, restrict the self-relation to R_Z = s⁻¹Z = t⁻¹Z. Invariance
restricts identity, inversion and composition. Its two projections are smooth base changes
(lem-sfb-self-relation-quotient-embedding, lem-sfb-stack-chartwise-smooth-etale-calculus).
Then Q = [Z/R_Z] is algebraic with smooth surjective atlas Z
(lem-sfb-smooth-groupoid-fppf-quotient).
3. Smoothness gives flatness and local finite presentation. Identify [U/R] with F using
lem-sfb-fppf-groupoid-stack-presentations, and apply the cartesian-source criterion
lem-sfb-groupoid-source-cartesian-quotient-square to get U ×_F Q = Z. The self-relation
embedding gives Q → F fully faithful and representable by algebraic spaces.
4. Test Q → F by T → F. The smooth surjective space T ×_F U admits jointly surjective
étale scheme lifts (lem-sfb-smooth-space-cover-etale-sections). On them the pullback is
a closed immersion by lem-weil-pbc-closed-immersion-base-change. Then
lem-sfb-space-closed-immersion-atlas-locality makes the original test a closed subscheme.
5. Take the strictly full essential image of Q → F. Full faithfulness lifts descent arrows
and their cocycles uniquely; effectiveness in Q makes this image a substack. Its equivalence
with Q gives algebraicity, the cartesian square and the asserted atlas.
6. Two closed substacks with the same pullback have identical object membership: test any
object after jointly surjective étale lifts to the atlas, where membership is factorization
through Z, and descend membership using stack descent and strict fullness. Fullness identifies
arrows. This proves injectivity; steps 2–5 prove surjectivity and the remaining assertions. -/
theorem invariantClosedSubstackDescent {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsAlgebraicModuliStack F)
    (U : Over S) (p : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (hp : IsSmoothModuliAtlas F U p) :
    ∃ e : ClosedModuliSubstack F ≃
        {I : U.left.IdealSheafData // IsInvariantClosedAtlasIdeal p I},
      ∀ W : ClosedModuliSubstack F,
        HasSchemeModuliBaseChange W.inclusion U p (closedAtlasScheme U (e W).val)
          (closedAtlasSchemeι U (e W).val) ∧
        IsAlgebraicModuliStack W.category ∧
        ∃ q : BasedFunctor (discreteModuli (yoneda.obj (closedAtlasScheme U (e W).val)))
            W.category,
          Nonempty (ModuliTwoIso (q.comp W.inclusion)
            ((discreteModuliMap (yoneda.map (closedAtlasSchemeι U (e W).val))).comp p)) ∧
          IsSmoothModuliAtlas W.category (closedAtlasScheme U (e W).val) q := by
  sorry

end CategoryTheory
