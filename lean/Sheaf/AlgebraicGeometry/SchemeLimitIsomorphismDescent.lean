/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.AlgebraicGeometry.DescendFlatFinitePresentation
import WeilConjectures.AlgebraicGeometry.DescendClosedImmersion
import WeilConjectures.AlgebraicGeometry.DescendSurjective
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Isomorphisms descend along affine-transition limits of qcqs schemes

Source: Stacks Project, Limits of Schemes, Tag 081E (lemma-descend-isomorphism),
in Situation 081D (situation-descent-property).
(blueprint: lem-sfb-scheme-limit-isomorphism-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A locally finitely presented morphism between qcqs schemes over one stage of an
inverse system of qcqs schemes with affine transitions is an isomorphism at some later
stage if its specified base change to the limit is an isomorphism.

Source: Stacks Project, Limits of Schemes, Tag 081E (lemma-descend-isomorphism),
in Situation 081D (situation-descent-property).
(blueprint: lem-sfb-scheme-limit-isomorphism-descent).

Proof:
1. The limit morphism is surjective, a closed immersion, and flat: an isomorphism
   is a homeomorphism and induces isomorphisms on structure sheaves and local rings
   (def-weil-surjective-morphism, def-weil-closed-immersion, def-weil-flat-morphism).
   Local finite presentation implies local finite type: a finitely presented algebra
   is finitely generated, and lem-weil-pbc-lft-pointwise-criterion passes from the
   pointwise affine formulation to local finite type (def-sbc-locally-finite-presentation,
   def-weil-finite-type-morphism).
2. Apply lem-weil-pbc-descend-flat-finite-presentation,
   lem-weil-pbc-descend-closed-immersion, and lem-weil-pbc-descend-surjective to obtain
   stages a, b, c above the initial index where the three properties hold respectively.
   The source, target, and initial base are qcqs, and the morphism is locally finitely
   presented (locally of finite type for closed-immersion descent).
3. Choose a common upper bound k. For r equal to a, b, or c, the transition B_k → B_r
   induces maps P_k → P_r and Q_k → Q_r compatible with h_k and h_r. The composition
   of transitions B_k → B_r → B_i₀ is B_k → B_i₀. Apply
   lem-weil-pbc-cartesian-square-pasting first to the iterated base changes defining
   Q_k and Q_r, and likewise to P_k and P_r: the resulting squares over B_k → B_r
   are cartesian. Apply pasting again to P_k → Q_k → B_k over P_r → Q_r → B_r.
   Its lower square and outer rectangle are cartesian, so its upper square is
   cartesian. Thus h_k is the base change of h_r along Q_k → Q_r
   (def-pc-fibre-product). The three base-change stability results
   lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-closed-immersion-base-change,
   and lem-weil-pbc-surjective-base-change give all three properties at k.
4. Apply lem-sfb-surjective-flat-closed-immersion-isomorphism to h_k. This proves
   invertibility of the specified morphism at a stage above i₀. -/
theorem exists_isIso_stage_of_limit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (P₀ Q₀ : Over (D.obj (op i₀))) (h₀ : P₀ ⟶ Q₀)
    [CompactSpace P₀.left] [QuasiSeparatedSpace P₀.left]
    [CompactSpace Q₀.left] [QuasiSeparatedSpace Q₀.left]
    [LocallyOfFinitePresentation h₀.left]
    (hB : IsIso (((Over.pullback (c.π.app (op i₀))).map h₀).left)) :
    ∃ (i : I) (hi : i₀ ≤ i),
      IsIso (((Over.pullback (D.map (homOfLE hi).op)).map h₀).left) := by
  sorry

end AlgebraicGeometry
