/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic

/-! # A zero neighbourhood for a section killed by inverse image

Source: Stacks Project, Tags 03PN (geometric stalks) and 03Q1 (pullback stalks).
(blueprint: lem-weil-pbc-etale-section-zero-neighbourhood)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

/-- If a section on an étale object becomes zero on a scheme mapping to that object,
then it is zero on an open neighbourhood of the image.
Source: Stacks Project, Tag 03PN, Definition 59.29.6 (filtered-colimit stalks),
and Tag 03Q1, lemma-stalk-pullback (3), including compatibility with the unit.
Proof: The zero locus of a section is open: a zero geometric germ is represented by
an étale neighbourhood of the given pointed object on which the section is zero,
by equality detection in the filtered colimit defining its stalk. The image of this neighbourhood
is open, and the neighbourhood covers its image. Sheaf separatedness therefore makes
the section zero on that image. Take the union of all opens on which the section is
zero. Sheaf separatedness on this open covering makes the section zero on the union.
For each point of T choose a geometric point above it. The inverse-image stalk
isomorphism, with its unit-germ compatibility and naturality for restriction,
carries the germ of the displayed canonical section to the original germ
on V. Its vanishing puts the image point in the zero locus. The uniqueness isomorphism
between H and the standard inverse image preserves the units, so the same reasoning
applies to the supplied adjunction. The empty scheme has empty image and permits the
empty open; for the zero section the whole object is a zero neighbourhood.
(blueprint: lem-weil-pbc-etale-section-zero-neighbourhood) -/
theorem etaleSection_zero_neighbourhood
    {X T : Scheme.{u + 1}} (V : X.Etale) (a : T ⟶ V.left)
    (p : T ⟶ X) (hp : a ≫ V.hom = p)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ p.Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology T.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (s : F.obj.obj (op V))
    (hs : ((hH.unit.app F).hom.app (op V) ≫
      (H.obj F).obj.map (MorphismProperty.Over.homMk
        (A := Scheme.Etale.mk (𝟙 T)) (B := p.Etale.obj V)
        (pullback.lift a (𝟙 T) (by
          change a ≫ V.hom = 𝟙 T ≫ p
          rw [Category.id_comp]
          exact hp))
        (by exact pullback.lift_snd _ _ _)).op) s = 0) :
    ∃ (U : V.left.Opens), Set.range a ⊆ (U : Set V.left) ∧
      F.obj.map (MorphismProperty.Over.homMk
        (A := Scheme.Etale.mk (U.ι ≫ V.hom)) (B := V) U.ι rfl).op s = 0 := by sorry
