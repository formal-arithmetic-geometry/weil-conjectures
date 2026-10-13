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

/-- For arbitrary nested opens A ≤ B of X, restriction on the inverse-image opens
commutes with each actual tail-stage cohomology transition, including its arbitrary
coefficient morphism φ. There is no condition on identities or compositions of φ.

Source: Stacks Project, Tag 01F7 (pullback and coefficient functoriality),
Tag 09YQ (restricted stage and cone maps); parent proof step 1.
(blueprint: lem-weil-pbc-etale-limit-stage-restriction-naturality)

Proof: Write f₀ for D.map of the opposite stage arrow. Functoriality of D and
composition of inverse-image opens give W_k = f₀⁻¹W_j for both W = A and W = B.
The defining equations for tailStageOpenMap show that its compositions with the
open inclusions agree with the corresponding compositions with f₀. Since the
open inclusions are monomorphisms, these restricted maps are the usual restrictions
of f₀, after transporting along the preceding equalities of opens.
Expand tailOpenCohomologyMapDegree and openSquareCoefficient. By Sheaf.H.map_comp_apply,
the transition on W is openCohomologyPullback f₀ W_j (F j.val) q followed by
Sheaf.H.map of the restriction of φ to W_k. Apply openCohomologyPullback_restriction
to A_j ≤ B_j. Restriction commutes with the coefficient map: expand
openCohomologyRestriction, use cohomologyMap_map on the inclusion A_k → B_k,
and combine the two Sheaf.H.map factors. Naturality of the inverse upperStarComp
comparison identifies their composites with the coefficient map on A_k followed
by restriction. Compose this coefficient equality with the pullback-restriction
equality. Substituting the actual transition definitions gives the displayed formula.
Proof irrelevance identifies the proofs of the open inclusions and commuting squares.
This works for empty or equal opens and for a zero coefficient morphism. -/
theorem tailOpenCohomologyMapDegree_restriction
    {X : Scheme.{u}} {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (q : ℕ) {i₀ : I} (g₀ : D.obj (op i₀) ⟶ X)
    (A B : X.Opens) (h : A ≤ B) (j k : Set.Ici i₀) (f : j ⟶ k)
      (x : Sheaf.H.{u + 1} ((upperStar AddCommGrpCat.{u + 1}
        (tailStageOpen D g₀ B j).ι).obj (F j.val)) q) :
      openCohomologyRestriction
        ((D.map (homOfLE k.property).op ≫ g₀).preimage_mono h) (F k.val) q
        ((tailOpenCohomologyMapDegree D g₀ B F φ q f).hom x) =
      (tailOpenCohomologyMapDegree D g₀ A F φ q f).hom (openCohomologyRestriction
        ((D.map (homOfLE j.property).op ≫ g₀).preimage_mono h) (F j.val) q x) := by sorry

end AlgebraicGeometry.Etale
