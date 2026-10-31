/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedExchange
public import WeilConjectures.AlgebraicGeometry.CondensedPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.CategoryTheory.DerivedTensorKoszulSymmetry

/-! # Proper product transpose for condensed derived module objects

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/
sk-thm-sf-kunneth-relative.proof.md, Coherence (i), final sentence
(blueprint: lem-sf-condensed-proper-product-transpose).

The ordinary unbounded projection, exchange and compositor maps define the product map.
Its transpose is the canonical tensor comparison followed by the two counits.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X Y B : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
  (K : DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
  (L : DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))

/-- The product map: signed symmetry, the `g` projection, signed symmetry, the
unit--square--counit exchange tensor identity, the `q` projection, and the direct-image
compositor, in that order. Here `p` and `q` are the canonical pullback projections and
`t = q ≫ g = p ≫ f`. Every factor is an existing canonical construction.
Source: the cited blueprint proof, Coherence (i), final sentence
(blueprint: lem-sf-condensed-proper-product-transpose). -/
def condensedProperProductMap :
    (moduleObjectDerivedPushforward Λ f).obj K ⊗
        (moduleObjectDerivedPushforward Λ g).obj L ⟶
      (moduleObjectDerivedPushforward Λ (pullback.snd f g ≫ g)).obj
        ((moduleObjectDerivedPullback Λ (pullback.fst f g)).obj K ⊗
          (moduleObjectDerivedPullback Λ (pullback.snd f g)).obj L) :=
  (derivedTensorKoszulSymmetry _ _ _).hom ≫
    moduleObjectProjectionMap Λ g L ((moduleObjectDerivedPushforward Λ f).obj K) ≫
    (moduleObjectDerivedPushforward Λ g).map
      ((derivedTensorKoszulSymmetry _ _ _).hom) ≫
    (moduleObjectDerivedPushforward Λ g).map
      ((moduleObjectDerivedExchange Λ
        (CommSq.mk (pullback.condition (f := f) (g := g)))).app K ⊗ₘ 𝟙 L) ≫
    (moduleObjectDerivedPushforward Λ g).map
      (moduleObjectProjectionMap Λ (pullback.snd f g)
        ((moduleObjectDerivedPullback Λ (pullback.fst f g)).obj K) L) ≫
    (rightDerivedLowerStarComp Λ (pullback.snd f g) g).hom.app _

/-- The product map is adjoint to the tensor of the two pulled-back counits.
Source: the cited blueprint proof, Coherence (i), final sentence
(blueprint: lem-sf-condensed-proper-product-transpose).

Proof, following the six DAG steps:
1. `lem-fix-condensed-pullback-coherence` identifies the specified adjunction for `t`
   with the composite adjunction for `q` then `g`, including its counit and tensorator.
2. `def-sfb-module-object-projection-map` identifies the transpose of each projection
   map with its tensorator followed by counit tensor identity; no projection is inverted.
3. Transpose along `g`. Naturality of its counit and the pullback braiding identity
   `lem-sf-condensed-derived-pullback-braiding` move the counit through the two symmetries,
   which cancel, leaving the exchange tensor the `g` counit after the tensorator.
4. Transpose along `q`. The defining projection equation and tensorator naturality give
   the tensor of the `q`-transpose of the exchange and the pulled-back `g` counit.
5. Expand the exchange using `def-weil-pbc-adjunction-mate`: counit naturality and the
   left triangle identity cancel its `q` unit and counit, leaving the square comparison
   followed by the pulled-back `f` counit.
6. Coherence identifies the composite tensorator with that for `t` and the square
   comparison with the `fp` compositor. This gives exactly the two-counit map below.
All objects are unbounded native derived modules and no exchange map is inverted. -/
theorem condensedProperProductTranspose [IsProper f] [IsProper g] :
    ((derivedUpperStarLowerStarAdjunction Λ (pullback.snd f g ≫ g)).homEquiv _ _).symm
        (condensedProperProductMap Λ f g K L) =
      ((leftDerivedUpperStarTensor Λ (pullback.snd f g ≫ g)).app
        ((moduleObjectDerivedPushforward Λ f).obj K)).app
          ((moduleObjectDerivedPushforward Λ g).obj L) ≫
        (((leftDerivedUpperStarComp Λ (pullback.snd f g) g).hom.app
            ((moduleObjectDerivedPushforward Λ f).obj K) ≫
          (moduleObjectDerivedPullbackSquareComparison Λ
            (CommSq.mk (pullback.condition (f := f) (g := g)))).hom.app
              ((moduleObjectDerivedPushforward Λ f).obj K) ≫
          (moduleObjectDerivedPullback Λ (pullback.fst f g)).map
            ((derivedUpperStarLowerStarAdjunction Λ f).counit.app K)) ⊗ₘ
          ((leftDerivedUpperStarComp Λ (pullback.snd f g) g).hom.app
              ((moduleObjectDerivedPushforward Λ g).obj L) ≫
            (moduleObjectDerivedPullback Λ (pullback.snd f g)).map
              ((derivedUpperStarLowerStarAdjunction Λ g).counit.app L))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
