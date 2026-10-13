/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone

/-! # Restricted cohomology arrow laws

Source: Stacks Project, Tags 09YQ and 01F7.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Canonical cohomology transition on the restricted stage opens.
Source: Stacks Project, Tags 09YQ and 01F7.
(blueprint: lem-weil-pbc-tail-open-cohomology-arrow-laws). -/
noncomputable def tailOpenCohomologyArrow {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) {X : Scheme.{u}} {i₀ : I}
    (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (n : ℕ) {j k : Set.Ici i₀} (f : j ⟶ k) :
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W j).ι).obj (F j.val)) n) ⟶
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W k).ι).obj (F k.val)) n) :=
  AddCommGrpCat.ofHom (cohomologyMap (tailStageOpenMap D g₀ W f) _ n) ≫
    AddCommGrpCat.ofHom (Sheaf.H.map
      (openSquareCoefficient (D.map (homOfLE (show j.val ≤ k.val from f.le)).op)
        (tailStageOpen D g₀ W j).ι (tailStageOpen D g₀ W k).ι
        (tailStageOpenMap D g₀ W f)
        (by simp only [tailStageOpenMap, Scheme.Hom.resLE_comp_ι])
        (F j.val) (F k.val)
        (φ (homOfLE (show j.val ≤ k.val from f.le)))) n)

/-- Restricted cohomology transitions preserve identities and composition.
Source: Stacks Project, Tags 09YQ (coherent systems) and 01F7 (functoriality).
(blueprint: lem-weil-pbc-tail-open-cohomology-arrow-laws).

Proof: Cancel the monomorphic stage-open inclusions to prove that tailStageOpenMap
preserves identities and reverses composites. Substitute hidentity in the identity
coefficient square. The two inverse-image unit laws cancel the original identity
comparison, leaving the canonical identity comparison on the restricted sheaf.
Cohomology pullback along identity followed by this comparison is the identity.
For composition substitute hcomposition, expand openSquareCoefficient, and use
naturality to move the first coefficient transition across the second square comparison.
Vertical pasting of inverse-image square isomorphisms identifies the comparisons with
that of the composite square. Cohomology pullback composition, naturality in the
coefficient sheaf, and functoriality of Sheaf.H.map then give the displayed composition.
No cocone, colimit, continuity or vanishing assertion is used. Empty opens and zero
coefficients are covered by the same functoriality equations. -/
theorem tailOpenCohomologyArrow_laws
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    {X : Scheme.{u}} (i₀ : I) (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens) (n : ℕ) :
    (∀ j : Set.Ici i₀, tailOpenCohomologyArrow D g₀ W F φ n (𝟙 j) = 𝟙 _) ∧
    (∀ (j k l : Set.Ici i₀) (f : j ⟶ k) (g : k ⟶ l),
      tailOpenCohomologyArrow D g₀ W F φ n (f ≫ g) =
        tailOpenCohomologyArrow D g₀ W F φ n f ≫
          tailOpenCohomologyArrow D g₀ W F φ n g) := by sorry

end AlgebraicGeometry.Etale
