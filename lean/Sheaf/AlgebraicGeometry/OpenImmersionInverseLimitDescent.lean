/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.DescendMonomorphism
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Gluing
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent

/-!
# Eventual descent of open immersions along qcqs inverse limits

Source: Stacks Project, Limits, Tag 0EUU in Situation 081D, and stability of open
immersions under base change (blueprint: lem-weil-pbc-descend-open-immersion-qcqs).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A locally finitely presented morphism between qcqs schemes over a stage of a
qcqs inverse system with affine transitions is an open immersion at every sufficiently
late stage if its base change to the limit is an open immersion. Neither its source
nor its target is required to be affine.

Source: Stacks Project, Limits, Tag 0EUU in Situation 081D; base-change persistence.
(blueprint: lem-weil-pbc-descend-open-immersion-qcqs).

Proof:
1. The limit morphism is etale and monic, by lem-weil-pbc-open-immersion-etale and
   lem-weil-pbc-open-immersion-monomorphism.
2. For each affine open of the target, cover its inverse image by affine opens
   (lem-weil-pbc-affine-opens-basis). The coordinate algebras are finitely presented
   by lem-weil-pbc-lfp-affine-opens-finite-presentation, hence finitely generated:
   the finite polynomial generators descend to generators of the quotient. This is
   locally finite type in def-weil-finite-type-morphism.
3. Apply lem-weil-pbc-descend-etale and lem-weil-pbc-descend-monomorphism to obtain
   stages a and b where the morphism is respectively etale and monic.
4. Choose a common upper bound i. The fibre-product universal property
   (def-pc-fibre-product) identifies X_i with X_c times_{Y_c} Y_i for c = a,b:
   on T-points, (x0,t) maps to ((x0,s_c t),(f0 x0,t)), and the inverse forgets
   the redundant coordinates. Thus f_i is etale by lem-weil-pbc-etale-scheme-base-change
   and monic by cancellation on the two pullback projections.
5. Monicity gives injectivity on points valued in every field, so f_i is radicial
   by def-weil-radicial-morphism. Apply lem-weil-pbc-radicial-etale-open to obtain
   that f_i is an open immersion.
6. For j >= i the same fibre-product identification gives X_j = X_i times_{Y_i} Y_j
   and identifies f_j with the projection to Y_j. Apply
   lem-weil-pbc-open-immersion-base-change to conclude for every such j. -/
theorem IsOpenImmersion.eventually_of_inverseLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj (op i₀)))
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFinitePresentation f₀.left]
    (hf : IsOpenImmersion (((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    ∃ (i : I) (hi : i₀ ≤ i), ∀ (j : I) (hij : i ≤ j),
      IsOpenImmersion
        (((Over.pullback (D.map (homOfLE (hi.trans hij)).op)).map f₀).left) := by
  sorry

end AlgebraicGeometry
