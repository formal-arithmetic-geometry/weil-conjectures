/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.AlgebraicGeometry.TailOpenCohomologyArrowLaws

/-! # Restricted cohomology leg naturality

Source: Stacks Project, Tags 09YQ and 01F7.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Canonical cohomology leg from a stage open to the limit open.
Source: Stacks Project, Tags 09YQ and 01F7.
(blueprint: lem-weil-pbc-tail-open-cohomology-leg-naturality). -/
noncomputable def tailOpenCohomologyCoconeLeg {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) {X : Scheme.{u}} {i₀ : I}
    (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (L : Cocone G) (n : ℕ) (j : Set.Ici i₀) :
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W j).ι).obj (F j.val)) n) ⟶
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1}
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι).obj L.pt) n) :=
  AddCommGrpCat.ofHom (cohomologyMap (tailLimitOpenMap D c g₀ W j) _ n) ≫
    AddCommGrpCat.ofHom (Sheaf.H.map
      (openSquareCoefficient (c.π.app (op j.val)) (tailStageOpen D g₀ W j).ι
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι (tailLimitOpenMap D c g₀ W j)
        (by simp only [tailLimitOpenMap, Scheme.Hom.resLE_comp_ι]) (F j.val) L.pt
        ((eG j.val).inv ≫ L.ι.app j.val)) n)

/-- The restricted cohomology legs commute with the restricted transitions.
Source: Stacks Project, Tags 09YQ and 01F7.
(blueprint: lem-weil-pbc-tail-open-cohomology-leg-naturality).

Proof: Precompose the cocone equation G.map f; L_k = L_j by eG_j.inv and substitute hG.
Cancel the inverse isomorphisms to obtain the original coefficient leg equation.
Restrict it along the limit-open inclusion. The projection square and transition square
paste to the projection square at j. Vertical pasting of inverse-image square comparisons
and naturality in the coefficient transition identify the restricted coefficient equation
with the composite of the restricted transition and restricted leg at k. The scheme
projections compose because both agree after the stage-open inclusion, by c.w.
Apply cohomology pullback composition, coefficient naturality and Sheaf.H.map composition
to this coefficient equation. The displayed naturality equality follows. The argument
uses arbitrary cocones, and includes empty opens and zero coefficients. -/
theorem tailOpenCohomologyCoconeLeg_naturality
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G)
    {X : Scheme.{u}} (i₀ : I) (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens) (n : ℕ)
    (j k : Set.Ici i₀) (f : j ⟶ k) :
    tailOpenCohomologyArrow D g₀ W F φ n f ≫
      tailOpenCohomologyCoconeLeg D c g₀ W F G eG L n k =
      tailOpenCohomologyCoconeLeg D c g₀ W F G eG L n j := by sorry

end AlgebraicGeometry.Etale
