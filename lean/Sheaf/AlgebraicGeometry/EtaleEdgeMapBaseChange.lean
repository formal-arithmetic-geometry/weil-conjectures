/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Compatibility of the étale cohomology edge map with base change

Source: Stacks Project, Etale Cohomology, Section 03SB, proof of Lemma 0A5D
(blueprint: lem-weil-pbc-edge-map-base-change).

The edge map is written as pullback on cohomology followed by the counit. In the finite
case, its bijectivity and that of the exchange followed by the base-changed edge map give
the two isomorphisms identifying the horizontal pullback maps.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The edge map commutes with cartesian base change, without any hypothesis on `f`.
Source: Stacks Project, Section 03SB, proof of Lemma 0A5D
(blueprint: lem-weil-pbc-edge-map-base-change).

Proof (steps 1--6 of the node):
1. Fix resolutions and unwind the edge maps as pullback followed by the counit. The
exchange map is the adjoint of the square isomorphism followed by pullback of the counit
(def-weil-pbc-underived-exchange, def-weil-pbc-inverse-image,
lem-weil-pbc-inverse-image-composition, def-weil-pbc-cohomology-pullback,
def-weil-pbc-kinjective-resolutions). Independence of resolutions follows from
lem-weil-pbc-cohomology-pullback-functorial, clause 1.
2. The induced maps `Sheaf.H.map` preserve composition and identities, by composition
of comparison lifts and functoriality of global sections and cohomology.
3. The adjunct-counit identity (lem-weil-pbc-adjunct-counit-identity) identifies pullback
of exchange followed by the counit with the square isomorphism followed by pullback
of the original counit; upstream this is `upperStar_map_baseChangeMap_app_counit`.
4. Naturality and composition of cohomological pullback
(lem-weil-pbc-cohomology-pullback-functorial, clauses 3 and 4) express the left side as
pullback along the diagonal followed by the inverse composition isomorphism and counit.
5. Apply the same naturality and composition clauses to the right side.
6. Substitute step 3 and cancel the composition isomorphisms. Both diagonal maps are
pullback along the same morphism, so the two sides agree. -/
theorem cohomology_edgeMap_baseChange
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    (cohomologyMap g' F q).comp
        ((Sheaf.H.map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app F) q).comp
          (cohomologyMap f ((lowerStar AddCommGrpCat.{u + 1} f).obj F) q)) =
      (Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f').counit.app
          ((upperStar AddCommGrpCat.{u + 1} g').obj F)) q).comp
        ((cohomologyMap f' ((lowerStar AddCommGrpCat.{u + 1} f').obj
          ((upperStar AddCommGrpCat.{u + 1} g').obj F)) q).comp
          ((Sheaf.H.map ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F) q).comp
            (cohomologyMap g ((lowerStar AddCommGrpCat.{u + 1} f).obj F) q))) := by
  sorry

/-- When `f` is finite and the underived exchange is invertible, the vertical comparison
maps in `cohomology_edgeMap_baseChange` are isomorphisms (bijective additive maps).
Thus that identity identifies `g`-pullback with `g'`-pullback through these isomorphisms.
Source: Stacks Project, Section 03SB, proof of Lemma 0A5D
(blueprint: lem-weil-pbc-edge-map-base-change).

Proof (step 7 of the node): finite morphisms are stable under base change
(lem-weil-pbc-finite-morphism-permanence), so `f'` is finite. Both edge maps are bijective
by lem-weil-pbc-finite-pushforward-cohomology. The exchange is an isomorphism, hence its
map on cohomology is bijective by step 2. Their composite is bijective. Step 6 then gives
the asserted identification of pullbacks through these two canonical isomorphisms. -/
theorem bijective_edgeMap_baseChange
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) [IsFinite f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (hEx : IsIso ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F)) :
    Function.Bijective
        ((Sheaf.H.map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app F) q).comp
          (cohomologyMap f ((lowerStar AddCommGrpCat.{u + 1} f).obj F) q)) ∧
      Function.Bijective
        ((Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f').counit.app
            ((upperStar AddCommGrpCat.{u + 1} g').obj F)) q).comp
          ((cohomologyMap f' ((lowerStar AddCommGrpCat.{u + 1} f').obj
            ((upperStar AddCommGrpCat.{u + 1} g').obj F)) q).comp
            (Sheaf.H.map ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F) q))) := by
  sorry

end AlgebraicGeometry.Etale
