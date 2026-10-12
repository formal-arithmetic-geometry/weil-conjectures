/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves

/-! # Finite-operation abelian charts near a point

Source: Stacks Project, Tag 03RU (definitions); agent-formulated finite-operation
refinement of steps 1--3 of `lem-weil-pbc-finite-constant-abelian-refinement`.
(blueprint: lem-weil-pbc-finite-constant-abelian-neighborhood).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

/-- A finite constant set chart admits, near each underlying point, a locally bijective
map from an actual constant abelian presheaf into the restricted abelian sheaf.
Source: Stacks Project, Tag 03RU (definitions only); agent-formulated argument,
steps 1--3 of the finite-operation refinement
(blueprint: lem-weil-pbc-finite-constant-abelian-neighborhood).

Proof: choose an algebraic closure of the residue field at the given point. Identify the
localized site at U with the small etale site of its domain. The constant set chart
identifies its labels with the underlying abelian stalk at this geometric point; transport
addition, zero and negation from that stalk to the labels. Constant labels give sections
of G. Equality of germs is equality on some pointed etale neighborhood. Apply this to
zero, every negative and every pairwise sum. There are finitely many comparisons, so
cofilteredness gives one pointed neighborhood where all hold. On every object above that
neighborhood, restriction of these sections is an additive map from the transported
abelian group; restriction compatibility makes these maps a natural transformation from
the constant abelian presheaf. Its underlying map is the set chart composed with the
constant-presheaf sheafification unit, after restriction. This is locally bijective:
restriction preserves local bijectivity and the chart is an isomorphism. The neighborhood
contains a point above the specified underlying point. The abelian group is finite since
its underlying labels are S. If S is empty, the geometric stalk, which contains zero,
cannot be identified with S, so this case is impossible. -/
theorem finite_constant_abelian_neighborhood {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : Y.Etale)
    (S : Type (u + 1)) [Finite S]
    (e : ((sheafCompose Y.smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G).over U ≅
        (constantSheaf (Y.smallEtaleTopology.over U) (Type (u + 1))).obj S)
    (x : U.left) :
    ∃ (V : U.left.Etale) (v : V.left), V.hom v = x ∧
      ∃ (M : AddCommGrpCat.{u + 1}), Finite M ∧
        ∃ e' : (constantSheaf
          (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ U.prop).obj V))
          (Type (u + 1))).obj (M : Type (u + 1)) ≅
            (sheafCompose
              (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ U.prop).obj V))
              (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
                (G.over ((MorphismProperty.Over.map ⊤ U.prop).obj V)),
          ∃ α : (Functor.const
            (Over ((MorphismProperty.Over.map ⊤ U.prop).obj V))ᵒᵖ).obj M ⟶
              (G.over ((MorphismProperty.Over.map ⊤ U.prop).obj V)).obj,
            Functor.whiskerRight α (CategoryTheory.forget AddCommGrpCat.{u + 1}) =
              toSheafify
                (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ U.prop).obj V))
                ((Functor.const
                  (Over ((MorphismProperty.Over.map ⊤ U.prop).obj V))ᵒᵖ).obj
                    (M : Type (u + 1))) ≫ e'.hom.hom := by sorry

end AlgebraicGeometry.Scheme
