/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q91
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Whiskering
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.LocallyFinitePresentationAffineLimitCriterion

/-!
# Surjective affine-limit tests for morphisms of algebraic spaces

Source: Stacks Project, Limits of Spaces, Tag 0CM6, `lemma-surjection-is-enough`;
Morphisms of Spaces, Tag 03XP, `definition-locally-finite-presentation`.
(blueprint: lem-sfb-space-surjective-affine-limit-criterion)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Surjectivity of the relative affine-limit comparison implies local finite presentation,
expressed on every pair of surjective étale scheme charts.

In the hypothesis, `x` and `y` are a compatible pair in
`X(T) ×_{Y(T)} colim Y(Tᵢ)`. A preimage is a colimit element `z` whose restrictions are
`x` and `y`. The first map is `colimit.desc` of the restriction cocone; the second is
`colim.map` of the natural transformation induced by `f`. Thus the hypothesis is precisely
surjectivity of the canonical comparison, with no uniqueness condition.
In the conclusion, `g` is the chart of `Y`, `h` is the chart of `X ×_Y V`, and `r`
is its scheme projection to `V`, identified by the Yoneda equation.

Source: Stacks Project, Limits of Spaces, Tag 0CM6; Morphisms of Spaces, Tag 03XP.
(blueprint: lem-sfb-space-surjective-affine-limit-criterion)

Proof:
1. Fix the two charts and write `q : U → X` and `r : U → V` for the projections.
For an affine inverse system over `V` and a map `a : T → U` over `V`, view everything
over `S` and form the compatible pair `(q a, [g bᵢ])`
[lem-trf-space-fibre-products-etale-covers].
2. The assumed surjectivity gives a stage map into `X`. Equality of its image class with
`[g bᵢ]` holds at a common later stage by the filtered-colimit element criterion. The two
stage maps then define `zⱼ : Tⱼ → X ×_Y V`, restricting to `h a`
[lem-weil-pbc-filtered-colimit-sets-elementwise].
3. The scheme test `E = Tⱼ ×_(X ×_Y V) U` is a scheme étale over `Tⱼ`. In particular it
is locally of finite presentation. The matching equality gives a map `T → E` over `Tⱼ`
[lem-trf-space-representable-etale-scheme-tests, def-weil-etale-morphism].
4. The tail of the inverse system over `Tⱼ` still has limit `T`. Apply the forward scheme
finite-presentation criterion to `E → Tⱼ` and represent the resulting colimit class by a
stage map `Tₖ → E`. Its projection `aₖ : Tₖ → U` restricts to `a` and is over `V`
[lem-weil-pbc-limit-affine-transition, lem-sfb-scheme-affine-limit-lfp-criterion,
lem-weil-pbc-filtered-colimit-sets-elementwise].
5. Every map over `V` has therefore descended to a stage. The surjective scheme criterion
makes `r` locally of finite presentation. Since both charts were arbitrary, this is the
asserted chart condition [lem-sfb-scheme-surjective-affine-limit-criterion]. -/
theorem locallyOfFinitePresentation_of_affine_limit_comparison_surjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hsurj : ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
      (D : Iᵒᵖ ⥤ Over S), (∀ i : Iᵒᵖ, IsAffine (D.obj i).left) →
      ∀ (c : Cone D), IsLimit c →
        ∀ (x : X.obj.obj.obj (op c.pt)) (y : colimit (D.rightOp ⋙ Y.obj.obj)),
          (f.hom.hom.app (op c.pt)) x =
            (colimit.desc (D.rightOp ⋙ Y.obj.obj)
              (Y.obj.obj.mapCocone (coconeRightOpOfCone c))) y →
          ∃ z : colimit (D.rightOp ⋙ X.obj.obj),
            (colimit.desc (D.rightOp ⋙ X.obj.obj)
              (X.obj.obj.mapCocone (coconeRightOpOfCone c))) z = x ∧
            (colim.map (Functor.whiskerLeft D.rightOp f.hom.hom)) z = y) :
    ∀ (V : Over S) (g : yoneda.obj V ⟶ Y.obj.obj),
      IsEtale g → IsSurjective g →
      ∀ (U : Over S) (h : yoneda.obj U ⟶ Limits.pullback f.hom.hom g),
        IsEtale h → IsSurjective h →
        ∀ r : U ⟶ V,
          h ≫ Limits.pullback.snd f.hom.hom g = yoneda.map r →
          LocallyOfFinitePresentation r.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
