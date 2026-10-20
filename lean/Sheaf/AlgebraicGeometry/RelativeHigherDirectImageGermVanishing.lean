/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.AlgebraicGeometry.RelativeHigherDirectImageExchange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Sheaf.AlgebraicGeometry.RelativeHigherDirectImageAffineSectionVanishing
import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-! # RelativeHigherDirectImageGermVanishing

Source: Stacks Project, Tag 0EYM. -/

@[expose] public section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar rightDerivedLowerStarPlus
  relativeHigherDirectImageExchange

/-- A stage higher-image germ killed at the limit is killed by a later transition.

Source: Stacks Project, Tag 0EYM, second proof, injectivity part (2).
(blueprint: lem-kun-relative-higher-image-germ-vanishing).

Proof: Work over an affine open pulled back from a stage and its cofinal tail.
Via eH_i and the inverse-image stalk comparison represent x by a stage
higher-image section on an affine etale neighbourhood of the image point.
Locally lift that section to the stage cohomology presheaf (03Q8). Its zero
image germ at the limit gives a further pointed etale refinement where its
sheafified image is zero. Local injectivity of sheafification supplies a second
refinement where the raw cohomology class is zero. This second refinement is
essential: vanishing after sheafification alone does not imply raw vanishing.
Refine by affine etale objects, descend the neighbourhood and its map to a
common later stage (0EYL), and consider its later base changes. Their fibre
products with the sources form a qcqs inverse system with affine transitions.
The restricted coefficients have the stated colimit because inverse image
commutes with colimits. Apply injectivity of cohomology continuity (09YQ): the
raw stage class vanishing at the limit dies at a later stage. Its image in the
stage higher image is zero. The exchange chart identity, naturality in the
coefficient map and hH identify this image germ with the prescribed transition
of x. Hence that transition kills x. The argument applies also in degree zero;
for the zero germ the identity arrow already suffices. -/
theorem relativeHigherDirectImage_germ_eventually_zero
    {I : Type u} [PartialOrder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (DV DB : Iᵒᵖ ⥤ Scheme.{u}) (η : DV ⟶ DB)
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DV.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DB.map a)]
    [∀ i : Iᵒᵖ, QuasiCompact (η.app i)]
    [∀ i : Iᵒᵖ, QuasiSeparated (η.app i)]
    (cV : Cone DV) (hcV : IsLimit cV) (cB : Cone DB) (hcB : IsLimit cB)
    (v : cV.pt ⟶ cB.pt)
    (hu : ∀ i : Iᵒᵖ, cV.π.app i ≫ η.app i = v ≫ cB.π.app i)
    (F : ∀ i : I, Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (a : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (DV.map a.op)).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (DV.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (DV.obj (op i))).hom.app (F i))
    (hφcomp : ∀ (i j k : I) (a : i ⟶ j) (b : j ⟶ k),
      φ (a ≫ b) =
        (upperStarComp AddCommGrpCat.{u + 1} (DV.map b.op) (DV.map a.op)
          (DV.map (a ≫ b).op) (DV.map_comp b.op a.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (DV.map b.op)).map (φ a) ≫ φ b)
    (A : I ⥤ Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eA : ∀ i : I, A.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op i))).obj (F i))
    (hA : ∀ (i j : I) (a : i ⟶ j), A.map a =
      (eA i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (cV.π.app (op j)) (DV.map a.op)
          (cV.π.app (op i)) (cV.w a.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op j))).map (φ a) ≫ (eA j).inv)
    (cA : Cocone A) (hcA : IsColimit cA) (q : ℕ)
    (H : I ⥤ Sheaf cB.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (cB.π.app (op i))).obj
        ((DerivedCategory.Plus.homologyFunctor
          (Sheaf (DB.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} (η.app (op i))).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
              (F i)))))
    (hH : ∀ (i j : I) (a : i ⟶ j), H.map a =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (cB.π.app (op j)) (DB.map a.op)
          (cB.π.app (op i)) (cB.w a.op).symm).hom.app
          ((DerivedCategory.Plus.homologyFunctor
            (Sheaf (DB.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
            ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} (η.app (op i))).obj
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
                (F i)))) ≫
        (upperStar AddCommGrpCat.{u + 1} (cB.π.app (op j))).map
          (relativeHigherDirectImageExchange ⟨η.naturality a.op⟩ (F i) (F j) (φ a) q) ≫
        (eH j).inv)
    (legs : H ⟶ (Functor.const I).obj
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf cB.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} v).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj cA.pt))))
    (hlegs : ∀ i : I, legs.app i = (eH i).hom ≫
      relativeHigherDirectImageExchange ⟨hu (op i)⟩ (F i) cA.pt
        ((eA i).inv ≫ cA.ι.app i) q)
    (s : cB.pt) (i : I)
    (x : ((cB.pt.uliftPointSmallEtale s).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj (H.obj i))
    (hx : (((cB.pt.uliftPointSmallEtale s).sheafFiber
      (A := AddCommGrpCat.{u + 1})).map (legs.app i)) x = 0) :
    ∃ (j : I) (a : i ⟶ j),
      (((cB.pt.uliftPointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).map (H.map a)) x = 0 := by
  classical
  let Φ := cB.pt.uliftPointSmallEtale s
  let G := H.obj i
  let L := (DerivedCategory.Plus.homologyFunctor
    (Sheaf cB.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} v).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj cA.pt))
  let m : G ⟶ L := legs.app i
  obtain ⟨U, u₀, z, hz⟩ := Φ.toPresheafFiber_jointly_surjective (P := G.obj) x
  have hzero : Φ.toPresheafFiber U u₀ L.obj (m.hom.app (op U) z) =
      Φ.toPresheafFiber U u₀ L.obj 0 := by
    rw [map_zero, ← Φ.toPresheafFiber_naturality_apply, hz]
    exact hx
  obtain ⟨W, g, w, hw, hW⟩ := (Φ.toPresheafFiber_eq_iff' U u₀ _ _).mp hzero
  have hWzero : m.hom.app (op W) (G.obj.map g.op z) = 0 := by
    rw [NatTrans.naturality_apply]
    simpa only [map_zero] using hW
  let B := Scheme.AffineEtale.Spec cB.pt
  obtain ⟨T, t, ⟨a⟩, u₁, hu₁⟩ := Φ.jointly_surjective _
    (B.is_cover_of_isCoverDense cB.pt.smallEtaleTopology W) w
  let V := B.obj a.obj
  have : IsAffine V.left := by
    dsimp only [V, B]
    rw [Scheme.AffineEtale.Spec_obj_left]
    infer_instance
  let v' := Φ.fiber.map a.lift u₁
  let zV := G.obj.map a.map.op (G.obj.map g.op z)
  have hzV : Φ.toPresheafFiber V v' G.obj zV = x := by
    rw [Φ.toPresheafFiber_w_apply, Φ.toPresheafFiber_w_apply]
    have hv : Φ.fiber.map a.map v' = w := by
      dsimp only [v']
      simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
        (congrArg (fun b ↦ Φ.fiber.map b u₁) a.fac).trans hu₁
    rw [hv, hw, hz]
  have hVzero : m.hom.app (op V) zV = 0 := by
    dsimp only [zV]
    rw [NatTrans.naturality_apply, hWzero, map_zero]
  obtain ⟨j, a, ha⟩ := relativeHigherDirectImage_affine_section_eventually_zero
    DV DB η cV hcV cB hcB v hu F φ hφid hφcomp A eA hA cA hcA q H eH hH
    legs hlegs V i zV hVzero
  refine ⟨j, a, ?_⟩
  rw [← hzV]
  change Φ.presheafFiber.map (H.map a).hom
    (Φ.toPresheafFiber V v' G.obj zV) = 0
  rw [Φ.toPresheafFiber_naturality_apply, ha, map_zero]

end AlgebraicGeometry.Etale
