/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.AlgebraicGeometry.EnlargedChartRingedMorphism
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
import Sheaf.AlgebraicGeometry.SpaceChangeBase
import Mathlib.CategoryTheory.Sites.Limits

/-! # Proper base change for set sheaves on algebraic spaces

Source: Stacks Project, More on Cohomology of Spaces, Tag 0DG0, and Étale Cohomology,
Tag 0A3U (blueprint: lem-sfb-space-proper-set-sheaf-base-change).

The map is the counit mate for the canonical small étale adjunctions. Composition
is normalized by the projections of the actual sheaf fibre products.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Composition on set direct images, normalized by the fibre-product projections.
Source: Stacks, Tags 03G2(2), 0A3U and 0DG0
(blueprint: lem-sfb-space-proper-set-sheaf-base-change). -/
def properSetDirectImageComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (enlargedSmallDirectImage_geometric.{u, w} f).choose.direct ⋙
      (enlargedSmallDirectImage_geometric.{u, w} g).choose.direct ≅
      (enlargedSmallDirectImage_geometric.{u, w} (f ≫ g)).choose.direct :=
  eqToIso (congrArg₂ (fun A B ↦ A ⋙ B)
      (enlargedSmallDirectImage_geometric f).choose_spec
      (enlargedSmallDirectImage_geometric g).choose_spec) ≪≫
    Functor.isoWhiskerLeft (enlargedSetEquivalence X).inverse
      (Functor.isoWhiskerLeft (enlargedDirectImage f _)
        (Functor.isoWhiskerRight (enlargedSetEquivalence Y).unitIso.symm
            (enlargedDirectImage g _ ⋙ (enlargedSetEquivalence Z).functor) ≪≫
          Functor.leftUnitor _) ≪≫
        Functor.isoWhiskerRight
          (Functor.sheafPushforwardContinuousComp'
            (enlargedBaseChange_composition f g).choose _ _ _ _)
          (enlargedSetEquivalence Z).functor) ≪≫
    (eqToIso (enlargedSmallDirectImage_geometric (f ≫ g)).choose_spec).symm

/-- The inverse-image comparison of a commuting square is conjugate to the
projection-normalized comparison of its direct images.
Source: Stacks, Tags 03G2(2), 0A3U and 0DG0
(blueprint: lem-sfb-space-proper-set-sheaf-base-change). -/
def properSetInverseImageSquare {Y Z Y' Z' : AlgebraicSpace S}
    (f : Y ⟶ Z) (g : Z' ⟶ Z) (f' : Y' ⟶ Z') (g' : Y' ⟶ Y)
    (h : g' ≫ f = f' ≫ g) :
    (enlargedSmallDirectImage_geometric.{u, w} g).choose.inverse ⋙
      (enlargedSmallDirectImage_geometric.{u, w} f').choose.inverse ≅
      (enlargedSmallDirectImage_geometric.{u, w} f).choose.inverse ⋙
        (enlargedSmallDirectImage_geometric.{u, w} g').choose.inverse :=
  (conjugateIsoEquiv
    ((enlargedSmallDirectImage_geometric.{u, w} f).choose.adj.comp
      (enlargedSmallDirectImage_geometric.{u, w} g').choose.adj)
    ((enlargedSmallDirectImage_geometric.{u, w} g).choose.adj.comp
      (enlargedSmallDirectImage_geometric.{u, w} f').choose.adj)).symm
    (properSetDirectImageComp g' f ≪≫
      eqToIso (congrArg (fun a ↦ (enlargedSmallDirectImage_geometric.{u, w} a).choose.direct) h) ≪≫
      (properSetDirectImageComp f' g).symm)

/-- The canonical exchange transformation, the mate of the inverse-image comparison
followed by the pullback of the counit of `f`. Its components are therefore natural
in arbitrary set sheaves.
Source: Stacks, Tags 0A3U and 0DG0
(blueprint: lem-sfb-space-proper-set-sheaf-base-change). -/
def properSetBaseChangeTransformation {Y Z Y' Z' : AlgebraicSpace S}
    (f : Y ⟶ Z) (g : Z' ⟶ Z) (f' : Y' ⟶ Z') (g' : Y' ⟶ Y)
    (h : g' ≫ f = f' ≫ g) :
    (enlargedSmallDirectImage_geometric.{u, w} f).choose.direct ⋙
      (enlargedSmallDirectImage_geometric.{u, w} g).choose.inverse ⟶
      (enlargedSmallDirectImage_geometric.{u, w} g').choose.inverse ⋙
        (enlargedSmallDirectImage_geometric.{u, w} f').choose.direct :=
  (mateEquiv (enlargedSmallDirectImage_geometric.{u, w} f).choose.adj
    (enlargedSmallDirectImage_geometric.{u, w} f').choose.adj
    (TwoSquare.mk _ _ _ _ (properSetInverseImageSquare f g f' g' h).hom)).natTrans

/-- Proper base change for every sheaf of sets, with its canonical natural map.
Source: Stacks Project, More on Cohomology of Spaces, Tag 0DG0
(blueprint: lem-sfb-space-proper-set-sheaf-base-change).

Proof: (1) Use the enlarged-site restriction and composition interfaces to localize
étale on both bases, then Zariski, reducing to affine schemes. Properness survives
these base changes (lem-sfb-space-proper-base-change). (2) Change the ground scheme
to Spec Z using lem-sfb-space-change-base-to-integers, and use weak Chow
(lem-sfb-space-weak-chow) to choose a proper surjective scheme cover Y₁ of Y.
The overlap Y₂ = Y₁ ×_Y Y₁ is a scheme by the representable diagonal. Both composites
to the affine base are proper by lem-sfb-space-proper-composition and proper base
change. (3) The cover and its base change give the two set-sheaf equalizers of
lem-sfb-space-proper-surjection-set-sheaf-equalizer, with projection-unit arrows.
(4) Direct image and the left exact inverse image preserve these equalizers;
lem-weil-pbc-site-sheaf-sets-limits-sectionwise computes them sectionwise.
Apply lem-sfb-scheme-proper-set-sheaf-base-change to Y₁ and Y₂. (5) Expand the
composition units and counits. Naturality and the triangle identities show that
the two scheme exchange isomorphisms commute with both projection-unit arrows,
and their map on equalizers is precisely the counit mate defined above.
(6) The isomorphisms and their inverses induce inverse maps on equalizers. Naturality
of units, counits and comparisons makes the result natural in the set sheaf.
The argument also covers empty spaces and uses no group or torsion structure. -/
theorem space_proper_set_sheaf_base_change {Y Z Y' Z' : AlgebraicSpace S}
    (f : Y ⟶ Z) (g : Z' ⟶ Z) (f' : Y' ⟶ Z') (g' : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (hf : MapIsProper f)
    (F : Sheaf Y.etaleTopology (Type (max (u + 1) w))) :
    IsIso ((properSetBaseChangeTransformation f g f' g' sq.w).app F) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
