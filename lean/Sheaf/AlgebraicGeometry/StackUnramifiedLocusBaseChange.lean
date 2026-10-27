/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage

/-! # The unramified open locus of a representable stack morphism

Source: Stacks Project, stacks-properties.tex, Tags 06M3 and 06M5(3);
spaces-morphisms.tex, Tags 05W2 and 03ZK
(blueprint: lem-sfb-stack-unramified-locus-base-change).

A full open substack of the discrete fibred groupoid of an algebraic space is its
open subspace. Equality after base change is expressed by equality of membership
predicates on the actual 2-fibre product. The scheme-chart inverse image retains
its representing equivalence and projection, rather than an unrelated open subset.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- A representable locally finite type map from a space to an algebraic stack has
 a largest unramified open, compatible with every representable stack base change.
 On every (possibly nonsurjective) étale scheme chart of a scheme base change, its
 inverse image is the union of the unramified open neighbourhoods.

Source: Stacks, Tags 06M3, 06M5(3), 05W2 and 03ZK
(blueprint: lem-sfb-stack-unramified-locus-base-change).

Proof:
1. Choose a smooth surjective scheme atlas A of the target. By
   lem-sfb-representable-pullback-over-space its pullback U to X is a space.
   Apply lem-sfb-space-unramified-locus-base-change to U → A. On the double
   overlap both pullbacks of its unramified open agree, by that same base-change
   formula and lem-sfb-stack-chartwise-smooth-etale-calculus.
2. Refine U by an étale scheme atlas P. The resulting P → X is smooth
   surjective. Apply lem-sfb-invariant-open-substack-descent to its invariant
   open. The descended open W is an open subspace of X: its scheme pullbacks
   are open subschemes, and representable pullback over X identifies it with a
   space. The pullback of W to U is the original unramified open, as can be
   checked on the étale cover P.
3. By lem-sfb-stack-representable-unramified-descent, W → Y is unramified:
   its atlas base change is unramified and the atlas is flat locally finitely
   presented. Any other unramified open pulls back into the largest open of
   U → A. The factorization criterion of invariant-open descent gives its
   containment in W.
4. For every space T → Y compare over A ×_Y T. Both the pullback of W and
   the unramified open of X_T → T pull back to the same unramified open there,
   by lem-sfb-space-unramified-locus-base-change. Refine the smooth surjective
   comparison by an étale scheme atlas and descend equality of opens. This
   uses no flatness hypothesis on T → Y.
5. Given representable Y' → Y, X' is a space by representable pullback.
   Its projection to Y' is locally finite type by the chart calculus. Construct
   its largest open by steps 1--3. On a smooth atlas of Y', step 4 identifies
   it with the inverse image of W. Invariant-open descent detects equality,
   proving the displayed equality of predicates on X'.
6. For a scheme base change T and étale chart V → X_T, step 4 identifies
   the pulled-back open with the largest unramified open of X_T → T.
   Its inverse image on V is unramified by lem-sfb-space-unramified-permanence.
   Conversely any unramified open J of V has open image I in X_T by
   lem-a1-space-etale-open-image. The surjective étale map J → I and
   lem-sfb-unramified-etale-compatible-charts make I → T unramified, hence
   I lies in the largest open. Thus every such J lies in its inverse image.
   This proves the union formula and the pointwise neighbourhood equivalence,
   without requiring the chart to be surjective. -/
theorem stack_unramified_locus_baseChange {S : Scheme.{u}}
    (X : AlgebraicSpace S) (Y : BasedCategory.{v₁, w₁} (Over S))
    (hY : IsAlgebraicModuliStack Y) (f : BasedFunctor (discreteModuli X.obj.obj) Y)
    (hf : IsRepresentableByAlgebraicSpaces f)
    (hft : ModuliSpaceTest @LocallyOfFiniteType f) :
    ∃ W : OpenModuliSubstack (discreteModuli X.obj.obj),
      ModuliSpaceTest @IsUnramified
        ((fullModuliInclusion (discreteModuli X.obj.obj) W.property).comp f) ∧
      (∀ Z : OpenModuliSubstack (discreteModuli X.obj.obj),
        ModuliSpaceTest @IsUnramified
          ((fullModuliInclusion (discreteModuli X.obj.obj) Z.property).comp f) →
          Z.IsContainedIn W) ∧
      (∀ (Y' : BasedCategory.{v₂, w₂} (Over S)) (hY' : IsAlgebraicModuliStack Y')
          (g : BasedFunctor Y' Y), IsRepresentableByAlgebraicSpaces g →
        ∃ W' : OpenModuliSubstack (moduliTwoFiberProduct g f),
          (∀ x : (moduliTwoFiberProduct g f).obj,
            W'.property x ↔ W.property ((moduliTwoFiberSnd g f).obj x)) ∧
          ModuliSpaceTest @IsUnramified
            ((fullModuliInclusion (moduliTwoFiberProduct g f) W'.property).comp
              (moduliTwoFiberFst g f)) ∧
          ∀ Z : OpenModuliSubstack (moduliTwoFiberProduct g f),
            ModuliSpaceTest @IsUnramified
              ((fullModuliInclusion (moduliTwoFiberProduct g f) Z.property).comp
                (moduliTwoFiberFst g f)) → Z.IsContainedIn W') ∧
      (∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) Y)
          (V : Over S)
          (c : BasedFunctor (discreteModuli (yoneda.obj V)) (moduliTwoFiberProduct t f))
          (r : V ⟶ T), IsEtaleModuliMap c →
        Nonempty (ModuliTwoIso (c.comp (moduliTwoFiberFst t f))
          (discreteModuliMap (yoneda.map r))) →
        ∃ (E : Over S) (j : E ⟶ V), IsOpenImmersion j.left ∧
          ∃ e : BasedFunctor (discreteModuli (yoneda.obj E))
              (moduliTwoFiberProduct (c.comp (moduliTwoFiberSnd t f))
                (fullModuliInclusion (discreteModuli X.obj.obj) W.property)),
            IsSchemeModuliBaseChange e j ∧
            Set.range j.left =
              ⋃ U : {U : V.left.Opens // IsUnramified (U.ι ≫ r.left)},
                (U.val : Set V.left) ∧
            ∀ x : V.left, x ∈ Set.range j.left ↔
              ∃ U : V.left.Opens, x ∈ U ∧ IsUnramified (U.ι ≫ r.left)) := by
  sorry

end CategoryTheory
