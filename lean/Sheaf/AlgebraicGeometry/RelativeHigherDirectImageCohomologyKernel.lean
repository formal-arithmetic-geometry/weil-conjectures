/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H5
-/
module
public import Sheaf.AlgebraicGeometry.RelativeHigherDirectImageExchange
public import Sheaf.AlgebraicGeometry.DerivedHomologySectionsComparison

/-! # Kernel of the chart-cohomology map to the higher-image colimit
Source: Stacks Project, Tag 0EYM, second proof, cohomology/sheaf diagram. -/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local irreducible] upperStar rightDerivedLowerStarPlus
  relativeHigherDirectImageExchange relativeHigherDirectImageDerivedMap

/-- A raw class with zero derived limit image maps to zero in the sheaf colimit.
This is the cohomological kernel argument, before finite-stage section detection.
Source: Stacks Project, Tag 0EYM, second proof, diagram and part (2).
(blueprint: lem-kun-relative-higher-image-cohomology-kernel).

Proof: Localize on inverse images of stage affine opens and pass to cofinal
upper tails. Open restriction, its exchange isomorphisms, and cube pasting
identify both coefficient and higher-image systems, including the actual mates.
On the finite-cover affine etale site, degree-zero continuity gives the section
formula L(U)=colim G_j(U_j) on a descended affine etale chart. The canonical
sheafification maps from chart cohomology to G_j induce h_U:colim P_j(U_j)→L(U).
The commutative chart identity identifies its composite with the limit map
with the limit sheafification map following cohomology continuity alpha_U.

Transport the section represented by z through the exact pullback homology
comparison. By the inverse-image construction, locally it comes from a stage
higher-image section. Lift that stage section to chart cohomology using 03Q8,
refine by affine etale objects, and descend the refinements and their maps by
0EYL. After pullback this raw representative and z have the same homology
section. Local injectivity of the raw-section comparison makes them equal
on a further refinement, so the displayed raw-zero hypothesis says that the
chart class has zero limit image. Descend this further refinement too.

The source fibre-product charts form a qcqs inverse system with affine
transitions and the expected limit. Restrict the coherent coefficients to
these charts; exact inverse-image composition and preservation of colimits
identify the limit coefficient. Cohomology continuity 09YQ is injective on
colim P_j, so the class is zero in that colimit. The map h_U sends it to zero
in L(U). Its definition through the section formula and the actual chart mate
identifies this with the colimit image of E.inv applied to the homology of z.
The refinements cover the original test object. Sheaf separatedness therefore
makes that image zero on the whole test object. This conclusion is in L, not
at a finite index; compactness and filteredness are used by its consumer to
obtain a stage. No exchange is assumed invertible except the etale/open
localization comparisons. The proof includes empty charts and q=0. -/
theorem relativeHigherDirectImage_cohomology_kernel
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
    (cH : Cocone H) (hcH : IsColimit cH) (i : I) :
    let Kᵢ := (upperStar AddCommGrpCat.{u + 1} (cB.π.app (op i))).mapDerivedCategoryPlus.obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} (η.app (op i))).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (F i)))
    let E : H.obj i ≅ (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj Kᵢ :=
      eH i ≪≫ relativeHigherDirectImageHomologyIso (η.app (op i))
        (cB.π.app (op i)) (F i) q
    ∀ (V : cB.pt.Etale) [IsAffine V.left]
      (z : ((derivedHomologySectionsFunctor cB.pt (q : ℤ)).obj Kᵢ).obj (op V)),
      ((derivedHomologySectionsFunctor cB.pt (q : ℤ)).map
        (relativeHigherDirectImageDerivedMap ⟨hu (op i)⟩ (F i) cA.pt
          ((eA i).inv ≫ cA.ι.app i))).app (op V) z = 0 →
      (cH.ι.app i).hom.app (op V)
        (E.inv.hom.app (op V)
          ((derivedHomologySectionsComparison cB.pt (q : ℤ) Kᵢ).app (op V) z)) = 0 := by
  sorry

end AlgebraicGeometry.Etale
