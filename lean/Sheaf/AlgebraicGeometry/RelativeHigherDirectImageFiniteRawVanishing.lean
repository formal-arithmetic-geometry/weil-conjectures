/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H5
-/
module
public import Sheaf.AlgebraicGeometry.RelativeHigherDirectImageExchange
public import Sheaf.AlgebraicGeometry.DerivedHomologySectionsComparison
import Sheaf.AlgebraicGeometry.RelativeHigherDirectImageCohomologyKernel
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyFilteredColimit

/-! # Eventual vanishing of a finite family of raw relative classes
Source: Stacks Project, Tag 0EYM, second proof, part (2). -/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] AbelianComparison.freeSheaf
attribute [local irreducible] upperStar rightDerivedLowerStarPlus
  relativeHigherDirectImageExchange relativeHigherDirectImageDerivedMap

private theorem section_eventually_zero
    {S : Scheme.{u}} {I : Type u} [SmallCategory I] [IsFiltered I]
    (H : I ⥤ Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (L : Cocone H) (hcL : IsColimit L) (W : S.Etale) [CompactSpace W.left]
    (i : I) (x : (H.obj i).obj.obj (op W))
    (hx : (L.ι.app i).hom.app (op W) x = 0) :
    ∃ (j : I) (a : i ⟶ j), (H.map a).hom.app (op W) x = 0 := by
  let e : AsSmall.{u + 1} I ≌ I := (AsSmall.equiv (C := I)).symm
  have hcL' : IsColimit (L.whisker e.functor) :=
    (Functor.Final.isColimitWhiskerEquiv e.functor L).symm hcL
  obtain ⟨j, a, ha⟩ := Scheme.exists_map_eq_zero_of_isColimit_ab hcL'
    (k := (AsSmall.up (C := I)).obj i) x hx
  exact ⟨e.functor.obj j, e.functor.map a, ha⟩

/-- Finitely many raw classes with zero derived image give higher-image sections
that vanish together after a stage transition.
Source: Stacks Project, Tag 0EYM, second proof, part (2); Tag 0738.
(blueprint: lem-kun-relative-higher-image-finite-raw-vanishing).

Proof: Form the ordinary sheaf colimit of H. The cohomological kernel lemma
makes the colimit image of each transported raw homology section zero. Fixed-site
filtered-colimit zero detection on the quasi-compact affine test object gives
one later arrow killing that section. For this detection, the conservative
family of etale points gives local stage zeros, quasi-compactness gives a finite
affine cover, filteredness gives a common stage, and sheaf separatedness gives
global zero. Apply this separately to every member of the finite family, then
use filteredness once more to find a common codomain with equal composites
from i. Functoriality of H transports each zero to that common codomain. This
also handles an empty family. The geometric and chart-cohomology argument,
including the unit's degree-zero section formula, is in the kernel lemma. -/
theorem relativeHigherDirectImage_finite_raw_eventually_zero
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
    (i : I) :
    let Kᵢ := (upperStar AddCommGrpCat.{u + 1} (cB.π.app (op i))).mapDerivedCategoryPlus.obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} (η.app (op i))).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (F i)))
    let E : H.obj i ≅ (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj Kᵢ :=
      eH i ≪≫ relativeHigherDirectImageHomologyIso (η.app (op i))
        (cB.π.app (op i)) (F i) q
    ∀ (J : Type u) [Finite J] (V : J → cB.pt.Etale) [∀ t, IsAffine (V t).left]
      (z : ∀ t, ((derivedHomologySectionsFunctor cB.pt (q : ℤ)).obj Kᵢ).obj (op (V t)))
      (_ : ∀ t, ((derivedHomologySectionsFunctor cB.pt (q : ℤ)).map
        (relativeHigherDirectImageDerivedMap ⟨hu (op i)⟩ (F i) cA.pt
          ((eA i).inv ≫ cA.ι.app i))).app (op (V t)) (z t) = 0),
      ∃ (j : I) (a : i ⟶ j), ∀ t,
        (H.map a).hom.app (op (V t))
          (E.inv.hom.app (op (V t))
            ((derivedHomologySectionsComparison cB.pt (q : ℤ) Kᵢ).app (op (V t)) (z t))) =
          0 := by
  classical
  intro Kᵢ E J _ V _ z hz
  have hsingle (t : J) : ∃ (j : I) (a : i ⟶ j),
      (H.map a).hom.app (op (V t))
        (E.inv.hom.app (op (V t))
          ((derivedHomologySectionsComparison cB.pt (q : ℤ) Kᵢ).app (op (V t)) (z t))) =
            0 := by
    apply section_eventually_zero H (colimit.cocone H) (colimit.isColimit H) (V t) i
    exact relativeHigherDirectImage_cohomology_kernel
      DV DB η cV hcV cB hcB v hu F φ hφid hφcomp A eA hA cA hcA q H eH hH
      (colimit.cocone H) (colimit.isColimit H) i (V t) (z t) (hz t)
  choose j a ha using hsingle
  obtain ⟨j', A, b, hb⟩ := IsFiltered.exists_comp_eq_of_finite a
  refine ⟨j', A, fun t ↦ ?_⟩
  rw [← hb t, H.map_comp]
  change (H.map (b t)).hom.app (op (V t))
    ((H.map (a t)).hom.app (op (V t))
      (E.inv.hom.app (op (V t))
        ((derivedHomologySectionsComparison cB.pt (q : ℤ) Kᵢ).app (op (V t)) (z t)))) = 0
  rw [ha t, map_zero]

end AlgebraicGeometry.Etale
