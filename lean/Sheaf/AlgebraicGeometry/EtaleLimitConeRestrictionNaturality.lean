/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCoconeDegree
public import Sheaf.AlgebraicGeometry.EtaleOpenCohomologyMaps

/-! # Naturality of a single restricted cohomology map

Source: Stacks Project, Tags 01F7 and 09YQ; the restricted square specialization
in the proof of the difference-map naturality lemma.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar cohomologyMap openCohomologyRestriction
  tailOpenCohomologyMapDegree tailOpenCohomologyLegDegree

set_option backward.isDefEq.respectTransparency true

/-- For arbitrary nested opens A ≤ B of X, restriction from B to A on the limit
inverse-image opens commutes with the actual cohomology leg from each tail stage.
The coefficient map is (eG j.val).inv followed by the cocone leg. The cone and
coefficient cocone need not be limiting or colimiting.

Source: Stacks Project, Tag 01F7 (pullback and coefficient functoriality),
Tag 09YQ (restricted stage and cone maps); parent proof step 1.
(blueprint: lem-weil-pbc-etale-limit-cone-restriction-naturality)

Proof: Put f₀ = c.π.app (op j.val). The cone equation for j.val → i₀, followed by g₀,
and composition of inverse-image opens give W_L = f₀⁻¹W_j for W = A and W = B.
The defining equations for tailLimitOpenMap show that its compositions with the
stage-open inclusions are the limit-open inclusions followed by f₀. Monicity of
the stage-open inclusions identifies these maps with the restrictions of f₀,
after transporting along the equalities of opens.
Expand tailOpenCohomologyLegDegree and openSquareCoefficient. Using Sheaf.H.map_comp_apply,
the leg on W is openCohomologyPullback f₀ W_j (F j.val) q followed by the cohomology
map of the restriction of the coefficient morphism (eG j.val).inv ≫ L.ι.app j.val.
Apply openCohomologyPullback_restriction to A_j ≤ B_j. Restriction commutes with this
coefficient morphism: expand openCohomologyRestriction, move the morphism past
cohomologyMap using cohomologyMap_map, combine the Sheaf.H.map factors, and apply
naturality of the inverse upperStarComp comparison to their coefficient composites.
Compose the two equalities and transport back to the supplied limit opens.
Proof irrelevance identifies the inclusion and commuting-square proofs. Only the
single coefficient morphism is used; no coefficient-system or cocone naturality
law is needed for this square. Empty or equal opens satisfy the same calculation. -/
theorem tailOpenCohomologyLegDegree_restriction
    {X : Scheme.{u}} {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (L : Cocone G) (q : ℕ) {i₀ : I} (g₀ : D.obj (op i₀) ⟶ X)
    (A B : X.Opens) (h : A ≤ B) (j : Set.Ici i₀)
      (x : Sheaf.H.{u + 1} ((upperStar AddCommGrpCat.{u + 1}
        (tailStageOpen D g₀ B j).ι).obj (F j.val)) q) :
      openCohomologyRestriction
        ((c.π.app (op i₀) ≫ g₀).preimage_mono h) L.pt q
        ((tailOpenCohomologyLegDegree D c g₀ B F G eG L q j).hom x) =
      (tailOpenCohomologyLegDegree D c g₀ A F G eG L q j).hom (openCohomologyRestriction
        ((D.map (homOfLE j.property).op ≫ g₀).preimage_mono h) (F j.val) q x) := by sorry

end AlgebraicGeometry.Etale
