/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Sheaf.AlgebraicGeometry.RestrictedAffineSingleMaps

/-! # Explicit maps for restricted degree-zero complexes

Source: Stacks Project, Tags 09Z1 and 0EZM.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The explicit cone comparison intertwines the restricted diagram transitions.
Source: Stacks Project, Tag 09Z1 proof (restriction to an affine etale object),
and Tag 03CB inverse-image composition comparisons.
(blueprint: lem-sbc-restricted-affine-single-cone-naturality).

Proof: Expand the explicit cone isomorphisms and restricted transitions, and substitute
hH for the coefficient diagram arrow. Write q_i for a restricted cone leg, r_i for
the stage second projection, and r for the cone point second projection. The pullback
projection identity is q_i followed by r_i equals r followed by c_i. The cone triangle
identifies q_j followed by the restricted transition with q_i. Apply upperStarComp_assoc
first to the triangle of the two original cone legs and the original transition, then
to the corresponding restricted triangle, and then to the second-projection squares.
Naturality moves the images of eH and of the coefficient transition through these
comparisons. Cancel inverse comparisons and the adjacent eH isomorphisms. Applying
singleFunctor and its natural inverse-image comparison gives the displayed equation.
This argument needs only hH, not the coefficient transition laws or any colimit. -/
theorem restrictedAffineSingleConeIso_naturality {S : Scheme.{v}}
    {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    (U : S.Etale) :
    let D' := restrictedAffineDiagram D U
    let c' := restrictedAffineCone D c U
    let K := restrictedAffineK D F U
    let G := restrictedAffineG D c H U
    let ψ := fun {i j : Iᵒᵖ} (f : j ⟶ i) ↦ restrictedAffineSingleTransition D F φ U f
    let eG := restrictedAffineSingleConeIso D c F H eH U
    ∀ (i j : Iᵒᵖ) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (c'.π.app j) (D'.map f)
            (c'.π.app i) (c'.w f).symm) (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (c'.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ (eG j).inv := by sorry

end AlgebraicGeometry.Etale
