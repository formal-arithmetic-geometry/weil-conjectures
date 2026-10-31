/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.AffineSpace

/-! # The standard Rees coordinates on the fibre at one -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

open Scheme.AffineZariskiSite in
private theorem reesChart_parameter {V S : Scheme.{u}}
    (g : V ⟶ S) (s : S ⟶ V) (U : V.AffineZariskiSite) :
    (colimit.ι (relativeGluingData s.ker.coequifibered_toReesPresheaf).functor U ≫
        Scheme.Hom.deformationSpaceProj g s).appTop
        (AffineSpace.coord S 0) =
      (Scheme.ΓSpecIso _).inv (s.ker.siteIdeal U).extendedReesAlgebraT := by
  rw [Scheme.Hom.deformationSpaceProj, Scheme.IdealSheafData.deformationSpaceToPolynomialSpec,
    ι_relativeGluingMap_assoc, Scheme.ι_polynomialSpecToAffineSpace_assoc,
    Scheme.polynomialSpecChart, AffineSpace.homOfVector_map,
    AffineSpace.comp_homOfVector, AffineSpace.homOfVector_appTop_coord,
    Function.comp_apply, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply]
  exact congrArg (fun x ↦ (Scheme.ΓSpecIso _).inv x)
    (Ideal.toExtendedReesAlgebra_X (I := s.ker.siteIdeal U))

open Scheme.AffineZariskiSite in
private theorem reesChart_originalCoordinate (n : Type u) (S : Scheme.{u})
    (U : (AffineSpace n S).AffineZariskiSite) (k : n) :
    (colimit.ι (relativeGluingData
        (AffineSpace.zeroSection n S).ker.coequifibered_toReesPresheaf).functor U ≫
      (AffineSpace.zeroSection n S).ker.deformationSpaceProj).appTop
        (AffineSpace.coord S k) =
      (Scheme.ΓSpecIso _).inv
        (algebraMap _ ((AffineSpace.zeroSection n S).ker.siteIdeal U).extendedReesAlgebra
          (Scheme.Hom.coordRes n S U k)) := by
  rw [ι_toBase, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have hfs : U.2.fromSpec.appTop =
      (AffineSpace n S).presheaf.map (homOfLE le_top).op ≫
        (Scheme.ΓSpecIso Γ(AffineSpace n S, U.1)).inv := by
    simp [Scheme.Hom.appTop, IsAffineOpen.fromSpec_app_of_le]
  change (Spec.map _).appTop (U.2.fromSpec.appTop (AffineSpace.coord S k)) = _
  rw [hfs, CommRingCat.comp_apply]
  erw [Scheme.specMap_appTop_ΓSpecIso_inv]
  rfl

open Scheme.AffineZariskiSite in
private theorem rees_originalCoordinates (n : Type u) (S : Scheme.{u}) :
    (AffineSpace.zeroSection n S).ker.deformationSpaceProj =
      AffineSpace.homOfVector
        (Scheme.Hom.deformationSpaceProj (AffineSpace n S ↘ S)
          (AffineSpace.zeroSection n S) ≫ (AffineSpace (ULift.{u} (Fin 1)) S ↘ S))
        (fun k ↦
          (Scheme.Hom.deformationSpaceProj (AffineSpace n S ↘ S)
            (AffineSpace.zeroSection n S)).appTop (AffineSpace.coord S 0) *
          (Scheme.Hom.deformationSpaceToAffineSpace n S).appTop
            (AffineSpace.coord (AffineSpace (ULift.{u} (Fin 1)) S) k)) := by
  refine colimit.hom_ext fun U ↦ AffineSpace.hom_ext ?_ fun k ↦ ?_
  · simp only [Category.assoc, AffineSpace.homOfVector_over,
      Scheme.Hom.deformationSpaceProj_over]
  · rw [AffineSpace.comp_homOfVector, AffineSpace.homOfVector_appTop_coord,
      Function.comp_apply, map_mul, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      reesChart_parameter, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      Scheme.Hom.ι_deformationSpaceToAffineSpace,
      Scheme.Hom.deformationSpaceToAffineSpaceChart, AffineSpace.homOfVector_appTop_coord,
      reesChart_originalCoordinate]
    erw [← map_mul]
    congr 1
    apply Subtype.ext
    change LaurentPolynomial.C (Scheme.Hom.coordRes n S U k) =
      LaurentPolynomial.T 1 *
        (LaurentPolynomial.C (Scheme.Hom.coordRes n S U k) * LaurentPolynomial.T (-1))
    simp only [mul_left_comm (LaurentPolynomial.T 1), ← LaurentPolynomial.T_add,
      Int.reduceAdd, LaurentPolynomial.T_zero, mul_one]

/-- The actual standard Rees coordinate map restricts at one to the affine-space
base-change map. Source: sk-thm-dnc, Local construction, x_j=t*u_j.
(blueprint: lem-trf-section-rees-one-coordinates).
Proof: on each affine chart, the original coordinate is the product of t and x_j/t
in the extended Rees algebra. The chart formulas glue by colimit extensionality.
Pull this equality back along the actual one-fibre map. Its parameter is one and its
map to the original affine space is the identity, so the divided coordinates are
the original coordinates. Affine-space extensionality then gives the displayed
map. No coordinate needs to exist, so the argument includes rank zero and empty bases. -/
theorem sectionRees_oneCoordinates (n : Type u) (S : Scheme.{u}) :
    Scheme.Hom.deformationSpaceOneFibre (AffineSpace n S ↘ S)
        (AffineSpace.zeroSection n S) ≫ Scheme.Hom.deformationSpaceToAffineSpace n S =
      AffineSpace.map n (AffineSpace.oneSection (ULift.{u} (Fin 1)) S) := by
  let r := Scheme.Hom.deformationSpaceOneFibre (AffineSpace n S ↘ S)
    (AffineSpace.zeroSection n S)
  have hr : r ≫ (AffineSpace.zeroSection n S).ker.deformationSpaceProj = 𝟙 _ := by
    simp only [r, Scheme.Hom.deformationSpaceOneFibre, Category.assoc,
      Scheme.Hom.deformationSpaceGeneric_toBase, pullback.lift_fst]
  have hq := (Scheme.Hom.isPullback_deformationSpaceOneFibre (AffineSpace n S ↘ S)
    (AffineSpace.zeroSection n S)).w
  apply AffineSpace.hom_ext
  · rw [Category.assoc, Scheme.Hom.deformationSpaceToAffineSpace_over,
      hq, AffineSpace.map_over]
  · intro k
    have hc := congrArg (fun f ↦ (r ≫ f).appTop (AffineSpace.coord S k))
      (rees_originalCoordinates n S)
    rw [hr] at hc
    simp only [AffineSpace.comp_homOfVector, AffineSpace.homOfVector_appTop_coord,
      Function.comp_apply, map_mul, ← Scheme.Hom.comp_appTop, ← CommRingCat.comp_apply] at hc
    have ht : r.appTop
        ((Scheme.Hom.deformationSpaceProj (AffineSpace n S ↘ S)
          (AffineSpace.zeroSection n S)).appTop (AffineSpace.coord S 0)) = 1 := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hq,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.oneSection, AffineSpace.homOfVector_appTop_coord]
      exact map_one _
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at hc
    rw [ht, one_mul] at hc
    simp only [Scheme.Hom.id_appTop, ConcreteCategory.id_apply] at hc
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.map_appTop_coord] using hc.symm

end AlgebraicGeometry.Etale
