/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-! # Compatible pullbacks of a fixed sheaf

Source: Stacks Project, Sites, Tag 03CB, and Etale Cohomology, Tag 09YQ.
(blueprint: lem-weil-pbc-compatible-pullback-sheaf-system).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Canonical pullback comparisons give a sheaf system, identified on a cone with a
constant diagram. No limit or quasi-compactness hypothesis is needed.
Source: Stacks Project, Sites, Tag 03CB (composition of morphisms of sites), and the
compatible inverse-image system in Etale Cohomology, Tag 09YQ.
(blueprint: lem-weil-pbc-compatible-pullback-sheaf-system).

Proof:
1. The transition from i to j is the inverse composition comparison for D.map f.op
   and v i. For an identity map, the left unit law for upperStarComp identifies this
   with upperStarId, including transport along D.map_id.
2. For f : i -> j and g : j -> k, apply the associativity law for upperStarComp to
   D.map g.op, D.map f.op and v i. Transport by D.map_comp and wv, take inverse
   components, and cancel the comparison for the first two maps. This is exactly
   the displayed composition equation for phi.
3. Apply the same calculation to d.pi at j, D.map f.op and v i. The cone equation
   identifies their first composite with d.pi at i. After transport by wLimit, it
   says that the comparison from stage i, followed by the transition and the inverse
   comparison at j, is the identity of vLimit inverse image of G. Thus S is the
   constant diagram with precisely the required comparison maps. -/
theorem compatiblePullbackSheafSystem
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (d : Cone D)
    (T : Scheme.{u}) (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (v : ∀ i : I, D.obj (op i) ⟶ T)
    (wv : ∀ (i j : I) (f : i ⟶ j), v j = D.map f.op ≫ v i)
    (vLimit : d.pt ⟶ T) (wLimit : ∀ i : I, vLimit = d.π.app (op i) ≫ v i) :
    let F := fun i : I ↦ (upperStar AddCommGrpCat.{u + 1} (v i)).obj G
    let φ := fun {i j : I} (f : i ⟶ j) ↦
      (upperStarComp AddCommGrpCat.{u + 1} (D.map f.op) (v i)
        (v j) (wv i j f)).inv.app G
    let K := (upperStar AddCommGrpCat.{u + 1} vLimit).obj G
    let S : I ⥤ Sheaf d.pt.smallEtaleTopology AddCommGrpCat.{u + 1} :=
      (Functor.const I).obj K
    let eS := fun i : I ↦
      (upperStarComp AddCommGrpCat.{u + 1} (d.π.app (op i)) (v i)
        vLimit (wLimit i)).app G
    (∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i)) ∧
    (∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k), φ (f ≫ g) =
      (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
        (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
      (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g) ∧
    (∀ (i j : I) (f : i ⟶ j), S.map f =
      (eS i).hom ≫
      (upperStarComp AddCommGrpCat.{u + 1} (d.π.app (op j)) (D.map f.op)
        (d.π.app (op i)) (d.w f.op).symm).hom.app (F i) ≫
      (upperStar AddCommGrpCat.{u + 1} (d.π.app (op j))).map (φ f) ≫ (eS j).inv) := by
  sorry

end AlgebraicGeometry.Etale
