/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
public import Sheaf.AlgebraicGeometry.SchemeUniverseEnlargement
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesUnit
import Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcValuativeDescent
import Sheaf.AlgebraicGeometry.EtaleSheafAlgebraicSpaceRealization
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme

/-!
# Representability of pro-etale local systems of sets

Source: Bhatt--Scholze, The pro-etale topology for schemes, Definition 7.3.1(1),(3)
and Lemma 7.3.9, implication Loc_X to Cov_X
(blueprint: lem-a1-proetale-local-system-representability).

The site is `X.ProEt`, with object universe `u + 1`, morphism universe `u`, and set
values in `Type (u + 1)`. The representing scheme lives in universe `u + 1` over
the canonical enlargement of `X`. This permits arbitrary sets of local sheets in
the sheaf universe. The original site is retained, and its objects and arrows are
enlarged only when evaluating the representing functor of points.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- The canonical functor from the original small pro-etale site to schemes over
the enlarged base, sending a structure map to its canonical universe enlargement.
Source: Bhatt--Scholze, Definition 7.3.1 and Lemma 7.3.9, functor of points;
Stacks Tag 01JA, affine gluing for universe enlargement
(blueprint: lem-a1-proetale-local-system-representability). -/
noncomputable def proEtaleUniverseLiftToOver (X : Scheme.{u}) :
    X.ProEt ⥤ Over (schemeUniverseLift.{u, u + 1} X) where
  obj U := Over.mk (schemeUniverseLiftMap.{u, u + 1} U.hom)
  map f := Over.homMk (schemeUniverseLiftMap.{u, u + 1} f.left) (by
    change schemeUniverseLiftMap.{u, u + 1} f.left ≫
      schemeUniverseLiftMap.{u, u + 1} _ = schemeUniverseLiftMap.{u, u + 1} _
    rw [← schemeUniverseLiftMap_comp]
    exact congrArg (schemeUniverseLiftMap.{u, u + 1}) f.w)
  map_id U := by
    apply Over.OverMorphism.ext
    change schemeUniverseLiftMap.{u, u + 1} (𝟙 U.left) = 𝟙 _
    let _ := schemeUniverseDiagram_hasColimit.{u, u + 1} U.left
    apply colimit.hom_ext
    intro j
    dsimp only [schemeUniverseLiftMap]
    rw [colimit.ι_desc]
    dsimp only [Cocone.whisker_ι, schemeUniverseLift]
    rw [Category.comp_id]
    change colimit.ι (schemeUniverseDiagram.{u, u + 1} U.left)
      ((CostructuredArrow.map (𝟙 U.left)).obj j) =
        colimit.ι (schemeUniverseDiagram.{u, u + 1} U.left) j
    let hj : j ⟶ (CostructuredArrow.map (𝟙 U.left)).obj j :=
      CostructuredArrow.homMk (𝟙 _) (by simp)
    have hw := colimit.w (schemeUniverseDiagram.{u, u + 1} U.left) hj
    change (schemeCoordinateRingLift.{u, u + 1}.op ⋙ Scheme.Spec).map (𝟙 j.left) ≫
      _ = _ at hw
    have hid := (schemeCoordinateRingLift.{u, u + 1}.op ⋙ Scheme.Spec).map_id j.left
    rw [hid, Category.id_comp] at hw
    exact hw
  map_comp f g := by
    apply Over.OverMorphism.ext
    change schemeUniverseLiftMap.{u, u + 1} (f.left ≫ g.left) =
      schemeUniverseLiftMap.{u, u + 1} f.left ≫ schemeUniverseLiftMap.{u, u + 1} g.left
    exact schemeUniverseLiftMap_comp f.left g.left

/-- A sheaf of arbitrary sets trivialized by a pro-etale cover is represented by
an etale geometric covering. The presheaf isomorphism gives bijections with
`Hom_X(U,Z)` natural in every object and arrow of the original site. The predicate
`ValuativeCriterion` asserts both existence and uniqueness of lifts for every
valuation ring and its fraction field. No quasi-compactness, finiteness, properness
or nonemptiness is required.

Source: Bhatt--Scholze, Definition 7.3.1(1),(3), p. 66, and Lemma 7.3.9,
pp. 67--68, Loc_X to Cov_X
(blueprint: lem-a1-proetale-local-system-representability).

Proof plan (the eight steps of the current DAG node):
1. Apply `lem-weil-pbc-proetale-locally-classical-etale-cover` to the given
   trivializations. Its arbitrary-set locally constant case gives an etale sheaf G
   and F isomorphic to its comparison inverse image, without contractible refinement.
2. By `lem-a1-etale-sheaf-algebraic-space-realization`, realize G by an etale
   algebraic space E over X. The comparison identifies F with its pro-etale functor
   of points and identifies restriction with the actual base changes E_{U_i}.
   Enlarge the universe to contain the presentation and its section-indexed charts.
3. The constant sheaf with value S is the coproduct of S copies of the terminal
   sheaf, by the constant-presheaf and sheafification adjunctions. Comparison inverse
   image preserves the terminal object and coproducts, using
   `lem-weil-pbc-left-adjoint-preserves-colimits`. It therefore preserves arbitrary
   constant set sheaves, including empty and infinite ones.
4. Combine step 2, step 3 and the trivializations. Full faithfulness from
   `det-pe-classical-sheaves-unit` lifts the isomorphisms to etale sheaves. Then
   `lem-galois-constant-sheaf-sets-representable` identifies the constants with the
   functors of D_i, the coproducts of S_i copies of U_i. Full faithfulness of
   etale-space realization yields actual isomorphisms E_{U_i} with D_i over U_i.
5. The self-product of D_i is the coproduct indexed by S_i times S_i. Its diagonal
   is the union of equal-index components and its complement the other components,
   so it is closed. A valuation-ring generic map selects one component. The base
   map into that component extends it, uniquely because Spec of a domain is
   connected. When S_i is empty there is no generic map. Use
   `lem-weil-pbc-scheme-coproduct-family` and the fibre-product construction.
6. The cover is fpqc by `def-weil-pbc-proetale-site`. Transport the separatedness
   and full valuation lifting property of step 5 along the actual isomorphisms
   E_{U_i} with D_i from step 4. Every scheme base change of their diagonals is a
   closed immersion by `lem-weil-pbc-closed-immersion-base-change`. Apply
   `lem-a1-space-fpqc-separated-valuative-descent` to descend both properties to E.
   This does not assert descent of arbitrary schemes.
7. Apply `lem-a1-separated-etale-space-scheme` to the etale space with closed
   diagonal. It is a scheme Z etale over X, without any quasi-compactness
   assumption. Retain the locally Noetherian hypothesis in the statement.
8. Compose the functor-of-points isomorphisms. Evaluation gives the requested
   bijections, and presheaf naturality gives compatibility with every site arrow.
   Transporting diagrams and their lifts across the representing isomorphism
   preserves exactly existence and uniqueness. No bound on the sheet sets is used.
-/
theorem proEtale_localSystem_representability (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F : Sheaf (ProEt.topology X) (Type (u + 1)))
    (I : Type (u + 1)) (U : I → X.ProEt)
    (hcover : (ProEt.topology X).CoversTop U) (S : I → Type (u + 1))
    (htriv : ∀ i : I, Nonempty
      (((proEtaleSetRestriction X (U i)).obj F) ≅
        (constantSheaf (ProEt.topology (U i).left) (Type (u + 1))).obj (S i))) :
    ∃ (Z : Scheme.{u + 1}) (q : Z ⟶ schemeUniverseLift.{u, u + 1} X),
      Etale q ∧
      Nonempty (F.obj ≅ (proEtaleUniverseLiftToOver X).op ⋙ yoneda.obj (Over.mk q)) ∧
      ValuativeCriterion q := by
  sorry

end AlgebraicGeometry.Scheme
