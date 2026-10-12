/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.AbelianHigherDirectImageMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-! # Composition of abelian higher direct image transitions
Source: Stacks Project, Tag 09Z1, canonical cohomology comparison maps. -/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Canonical abelian higher direct image transitions respect coefficient composition.
Source: Stacks Project, Tag 09Z1, functoriality of the comparison maps.
(blueprint: lem-sbc-abelian-higher-direct-image-transition-comp).

Proof: Expand both transitions before degree-p homology. Naturality moves the
second derived adjunction unit past the first coefficient map. The triangle
identity cancels the intermediate counit with that unit. The associativity
coherence of inverse-image composition and its comparison with the single
functor identifies the remaining factors with the transition for f followed
by g. Substitute hφcomp and D.map_comp (in the opposite order). Apply the
homology functor, which preserves composition. Identity and structure-map
proof transports agree by proof irrelevance. No limit or qcqs hypothesis is used.
This also applies when a stage or sheaf is zero. -/
theorem abelianHigherDirectImage_transition_comp {S : Scheme.{v}}
    {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (p : ℕ) {i j k : I} (f : i ⟶ j) (g : j ⟶ k) :
    abelianHigherDirectImageMap (D.map (f ≫ g).op).left (D.obj (op i)).hom
        (D.obj (op k)).hom (Over.w (D.map (f ≫ g).op)) p (F i) (F k) (φ (f ≫ g)) =
      abelianHigherDirectImageMap (D.map f.op).left (D.obj (op i)).hom
          (D.obj (op j)).hom (Over.w (D.map f.op)) p (F i) (F j) (φ f) ≫
        abelianHigherDirectImageMap (D.map g.op).left (D.obj (op j)).hom
          (D.obj (op k)).hom (Over.w (D.map g.op)) p (F j) (F k) (φ g) := by sorry

end AlgebraicGeometry.Etale
