/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.AlgebraicGeometry.SchemeUniverseEnlargement
public import Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
public import Sheaf.AlgebraicGeometry.EtaleSheafAlgebraicSpaceRealization
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesUnit
import Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison

/-!
# Realization with arbitrary sheet sets after universe enlargement

Source: Stacks Project, Tag 0GF6, including its size footnote; Bhatt--Scholze,
Lemmas 5.1.1, 5.1.2 and 5.4.1
(blueprint: lem-a1-universe-enlarged-etale-realization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

open AlgebraicGeometry.Scheme

/-- The functorial packaging of the canonical enlargement used by the realization API. -/
noncomputable def schemeUniverseLiftFunctor : Scheme.{u} ⥤ Scheme.{u + 1} where
  obj := schemeUniverseLift.{u, u + 1}
  map := schemeUniverseLiftMap.{u, u + 1}
  map_id := by
    intro X
    let _ := schemeUniverseDiagram_hasColimit.{u, u + 1} X
    apply colimit.hom_ext
    intro j
    dsimp only [schemeUniverseLiftMap]
    rw [colimit.ι_desc]
    dsimp only [Cocone.whisker_ι, schemeUniverseLift]
    rw [Category.comp_id]
    change colimit.ι (schemeUniverseDiagram.{u, u + 1} X)
      ((CostructuredArrow.map (𝟙 X)).obj j) =
        colimit.ι (schemeUniverseDiagram.{u, u + 1} X) j
    let hj : j ⟶ (CostructuredArrow.map (𝟙 X)).obj j :=
      CostructuredArrow.homMk (𝟙 _) (by simp)
    have hw := colimit.w (schemeUniverseDiagram.{u, u + 1} X) hj
    change (schemeCoordinateRingLift.{u, u + 1}.op ⋙ Scheme.Spec).map (𝟙 j.left) ≫
      _ = _ at hw
    rw [(schemeCoordinateRingLift.{u, u + 1}.op ⋙ Scheme.Spec).map_id, Category.id_comp] at hw
    exact hw
  map_comp := by
    intro X Y Z f g
    exact schemeUniverseLiftMap_comp f g


/-- Realize an arbitrary large-valued small-etale sheaf over the enlarged base.
The local conclusion identifies the actual base-changed functor of points with
that of the coproduct whenever its pro-etale restriction is constant. There is no
covering or Noetherian hypothesis.

Source: Stacks Project, Tag 0GF6 and its size footnote; Bhatt--Scholze,
Lemmas 5.1.1, 5.1.2 and 5.4.1; Stacks Tags 03P5 and 03YW
(blueprint: lem-a1-universe-enlarged-etale-realization).

Proof:
1. Use all pairs of a small etale object and a section of G as representable
   generators. Both the object collection and its section sets are in universe
   u + 1. Enlarge each generator by the affine-colimit construction and take
   their coproduct in Scheme.{u + 1}. The equality relation between the two
   universal sections on its self-product is represented by an open subscheme:
   etale-locally on both generators this is the support of the corresponding
   subsheaf of the terminal etale sheaf, as in Stacks Tag 0GF6.
2. The resulting etale equivalence relation gives an algebraic space E over the
   enlarged X. Its small-etale sheaf on original test objects is G: local
   generator sections give surjectivity, and the equality relation gives precisely
   its kernel pair. Etale-source descent gives chartwise etaleness. This is the
   quotient proof of Tag 0GF6 with generators in the necessary larger universe.
3. The same atlas and kernel pair describe the pro-etale sheaf of points. The
   comparison inverse image preserves their coequalizer and takes representable
   generators to their pro-etale Hom sheaves (Bhatt--Scholze 5.1.1). This gives
   the first natural presheaf isomorphism, including every site arrow.
4. Base change this construction to any original weakly etale U. Comparison
   commutes with this restriction (Bhatt--Scholze 5.4.1). Comparison preserves
   arbitrary constants: express a constant as the coproduct of copies of the
   terminal sheaf and use finite-limit and colimit preservation. Full faithfulness
   (Bhatt--Scholze 5.1.2) lifts a given constant pro-etale trivialization to the
   etale sheaves. The constant etale sheaf is represented by the coproduct of S
   copies of the enlarged U (Tags 03P5 and 03YW). Full faithfulness in the
   realization construction identifies these algebraic spaces over enlarged U;
   its Yoneda isomorphism on all schemes is the last displayed conclusion.
   Empty S yields the empty coproduct; infinite S needs no compactness. -/
theorem etaleSheaf_universeEnlarged_realization (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    ∃ E : EtaleSpaces (schemeUniverseLift.{u, u + 1} X),
      Nonempty
        (((Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
          (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj G).obj ≅
          (Scheme.ProEt.forget X ⋙ Over.post schemeUniverseLiftFunctor).op ⋙
            E.obj.obj.obj) ∧
      ∀ (U : X.ProEt) (S : Type (u + 1)),
        Nonempty
          (((Scheme.proEtaleSetRestriction X U).obj
            ((Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
              (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj G)) ≅
            (constantSheaf (Scheme.ProEt.topology U.left) (Type (u + 1))).obj S) →
        Nonempty
          (yoneda.obj (Over.mk (Sigma.desc
              (fun _ : S ↦ 𝟙 (schemeUniverseLift.{u, u + 1} U.left)))) ≅
            (Over.map (schemeUniverseLiftMap.{u, u + 1} U.hom)).op ⋙ E.obj.obj.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
