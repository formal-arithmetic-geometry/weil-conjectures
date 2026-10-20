/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NW and H5
-/
module

public import Sheaf.AlgebraicGeometry.RelativeHigherDirectImageExchange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Sheaf.AlgebraicGeometry.RelativeHigherDirectImageRawLocalDescent
import Sheaf.AlgebraicGeometry.DerivedHomologySectionsComparison

/-! # RelativeHigherDirectImageGermDescent

Source: Stacks Project, Tag 0EYM. -/

@[expose] public section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] AbelianComparison.freeSheaf
  Functor.mapDerivedCategoryPlusHomologyFunctorIso

attribute [local irreducible] upperStar rightDerivedLowerStarPlus
  relativeHigherDirectImageExchange relativeHigherDirectImageDerivedMap

/-- A germ in the limit higher direct image has a representative at some stage.

Source: Stacks Project, Tag 0EYM, second proof, surjectivity part (1).
(blueprint: lem-kun-relative-higher-image-germ-descent).

Proof: Restrict to inverse images of an affine open at a stage, and replace the
index by its cofinal tail. The restricted source schemes are qcqs and all
transitions are affine. Represent the germ by a section on an affine etale
neighbourhood, then locally lift this section through the sheafification of the
cohomology presheaf (03Q8). Refine once more by affine etale objects and descend
one neighbourhood containing the marked geometric point to a stage (0EYL).
For its later base changes U_j, the schemes V_j times_{B_j} U_j are qcqs with
affine transitions and limit V times_B U. Pull the coefficients F_j to these
schemes. Inverse-image composition and preservation of colimits identify their
limit coefficient with the restriction of cA.pt. Cohomology continuity (09YQ)
represents the lifted degree-q class at some stage. The cohomology-presheaf
map sends that class to a stage higher-image section, whose germ determines an
element of H_i via eH_i and the pullback-stalk comparison. The commutative
exchange chart identity, with the coefficient coprojection, identifies its image
under legs_i with the initial germ. All maps are the specified mate maps;
no exchange map is presumed invertible. The proof includes q=0, zero sheaves,
and empty schemes (where there is no point s). -/
theorem relativeHigherDirectImage_germ_descent
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
    (_hH : ∀ (i j : I) (a : i ⟶ j), H.map a =
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
    (s : cB.pt) :
    ∀ y : ((cB.pt.uliftPointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj (((DerivedCategory.Plus.homologyFunctor
        (Sheaf cB.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} v).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj cA.pt)))),
      ∃ (i : I) (x : ((cB.pt.uliftPointSmallEtale s).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj (H.obj i)),
        (((cB.pt.uliftPointSmallEtale s).sheafFiber
          (A := AddCommGrpCat.{u + 1})).map (legs.app i)) x = y := by
  classical
  intro y
  let S := cB.pt
  let K := (rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} v).obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj cA.pt)
  let Φ := S.uliftPointSmallEtale s
  let P := (derivedHomologySectionsFunctor S (q : ℤ)).obj K
  let τ := derivedHomologySectionsComparison S (q : ℤ) K
  have hτ := ((derivedHomologySectionsComparison_spec S (q : ℤ)).1 K).2
  have : LocallySmall.{u + 1} S.Etale := locallySmall_max.{u + 1, u, u + 1}
  have := hτ
  obtain ⟨y', hy'⟩ := Φ.toPresheafFiber_map_surjective τ y
  obtain ⟨U, u₀, z, hz⟩ := Φ.toPresheafFiber_jointly_surjective (P := P) y'
  obtain ⟨W, a, w, hw, i, t, ht⟩ := relativeHigherDirectImage_raw_local_factorization
    DV DB η cV hcV cB hcB v hu F φ hφid hφcomp A eA hA cA hcA q s U u₀ z
  let Kᵢ := (upperStar AddCommGrpCat.{u + 1} (cB.π.app (op i))).mapDerivedCategoryPlus.obj
    ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} (η.app (op i))).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (F i)))
  let E : H.obj i ≅ (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj Kᵢ :=
    eH i ≪≫ relativeHigherDirectImageHomologyIso (η.app (op i))
      (cB.π.app (op i)) (F i) q
  let m := relativeHigherDirectImageDerivedMap ⟨hu (op i)⟩ (F i) cA.pt
    ((eA i).inv ≫ cA.ι.app i)
  let Hq := DerivedCategory.Plus.homologyFunctor
    (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
  have hleg : legs.app i = E.hom ≫ Hq.map m := by
    rw [hlegs, relativeHigherDirectImageExchange_eq_homology]
    simp only [E, Hq, m, S, Iso.trans_hom, Category.assoc]
  have hcomp : E.inv ≫ legs.app i = Hq.map m := by
    rw [hleg, Iso.inv_hom_id_assoc]
  let τᵢ := derivedHomologySectionsComparison S (q : ℤ) Kᵢ
  let z' := P.map a.op z
  let t' := E.inv.hom.app (op W) (τᵢ.app (op W) t)
  have hsection : (legs.app i).hom.app (op W) t' = τ.app (op W) z' := by
    change ((E.inv ≫ legs.app i).hom.app (op W)) (τᵢ.app (op W) t) = _
    rw [hcomp]
    exact ((derivedHomologySectionsComparison_spec S (q : ℤ)).2 m W t).trans
      (congrArg (τ.app (op W)) ht)
  refine ⟨i, Φ.toPresheafFiber W w (H.obj i).obj t', ?_⟩
  change Φ.presheafFiber.map (legs.app i).hom
    (Φ.toPresheafFiber W w (H.obj i).obj t') = y
  rw [Φ.toPresheafFiber_naturality_apply, hsection]
  change Φ.toPresheafFiber W w (Hq.obj K).obj (τ.app (op W) z') = y
  rw [← Φ.toPresheafFiber_naturality_apply τ W w]
  have hw' : Φ.toPresheafFiber W w P z' = y' := by
    dsimp only [z']
    rw [Φ.toPresheafFiber_w_apply, hw]
    exact hz
  rw [hw']
  exact hy'

end AlgebraicGeometry.Etale
