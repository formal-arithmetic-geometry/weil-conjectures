/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalData

import Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateSubschemes
import Mathlib.RingTheory.MvPolynomial.Ideal
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSectionChart
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartPolynomial
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical

/-! # Coordinate geometry of projective space over a field

Source: Stacks Project, Tags 01NG, 01MS, 01WR, 01WX.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

open ProjectiveSpace

attribute [local irreducible] coordinateSection twist Scheme.Modules.Hom.zeroLocus

private theorem polynomial_constants_bijective (σ R : Type u) [CommRing R] :
    Function.Bijective ((Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R)).comp
      MvPolynomial.C) := by
  let I := MvPolynomial.idealOfVars σ R
  let q := Ideal.Quotient.mk I
  let ev := MvPolynomial.eval₂Hom (RingHom.id R) (fun _ : σ ↦ (0 : R))
  have hev : I ≤ RingHom.ker ev := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    simp [ev, RingHom.mem_ker]
  let e := Ideal.Quotient.lift I ev hev
  have he (a : R) : e (q (MvPolynomial.C a)) = a := by
    simp [e, q, ev]
  have hq (p : MvPolynomial σ R) : q p = q (MvPolynomial.C (ev p)) := by
    have heq : (q.comp MvPolynomial.C).comp ev = q := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [ev]
      · intro i
        have hi : q (MvPolynomial.X i) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
        simp [ev, hi]
    exact (RingHom.congr_fun heq p).symm
  constructor
  · intro a b hab
    exact (he a).symm.trans ((congrArg e hab).trans (he b))
  · intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨ev p, (hq p).symm⟩
private theorem coordinate_divisor (I : Type u) (R : Type u) [CommRing R] (i : I) :
    (Scheme.Modules.Hom.zeroLocus (coordinateSection I (Spec (.of R)) i)).IsInvertible := by
  classical
  have : SheafOfModules.IsInvertible.{u, u, u} (𝟙_ (ℙ(I; Spec (.of R))).Modules) :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ (ℙ(I; Spec (.of R))).Modules)
  intro x
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_standardOpen I (Spec (.of R))).ge (show x ∈ ⊤ from trivial))
  let U : (ℙ(I; Spec (.of R))).affineOpens :=
    ⟨standardOpen I (Spec (.of R)) j, isAffineOpen_standardOpen I (Spec (.of R)) j⟩
  refine ⟨U, hj, ?_⟩
  have hid : (coordinateSection I (Spec (.of R)) i).zeroLocus.ideal U =
      Ideal.span {coordRatio I (Spec (.of R)) j i} :=
    Scheme.Modules.Hom.ideal_zeroLocus (coordinateSection I (Spec (.of R)) i) U
      (Scheme.Modules.isFreeGenerator_one (X := ℙ(I; Spec (.of R))) U.1)
      (isFreeGenerator_twistGenerator I (Spec (.of R)) 1 j)
      (coordinateSection_app_standardOpen I (Spec (.of R)) i j)
  rw [hid]
  by_cases hij : i = j
  · subst i
    rw [coordRatio_self]
    exact Ideal.isRegularPrincipal_span_singleton_of_isRegular isRegular_one
  · have hX := Ideal.isRegularPrincipal_span_singleton_of_isRegular
        (MvPolynomial.isRegular_X (R := R) (σ := {k : I // k ≠ j}) (n := ⟨i, hij⟩))
    have h := hX.map_of_bijective
      (f := (chartRingEquiv I R j).toRingHom) (chartRingEquiv I R j).bijective
    rw [Ideal.map_span, Set.image_singleton] at h
    change (Ideal.span {(chartRingEquiv I R j)
      (MvPolynomial.X ⟨i, hij⟩)}).IsRegularPrincipal at h
    simpa only [chartRingEquiv_X] using h
private theorem lineBundle_of_coordinate_divisor
    {X : Scheme.{u}} {L : X.Modules} [L.IsInvertible]
    (s : Scheme.Modules.unit X ⟶ L) (hs : s.zeroLocus.IsInvertible) :
    Nonempty (s.zeroLocus.toModules.dual ≅ L) := by
  have : SheafOfModules.IsInvertible.{u, u, u} (Scheme.Modules.unit X) :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ X.Modules)
  have : SheafOfModules.IsInvertible.{u, u, u} L :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible L
  obtain ⟨e⟩ := Scheme.Modules.Hom.nonempty_iso_dual_toModules_tensorObj s hs
  exact ⟨(e ≪≫ ρ_ _).symm⟩
private noncomputable def coordinateIndex (n : ℕ) :
    {j : ULift.{u} (Fin (n + 1)) // j ≠ ⟨0⟩} ≃ ULift.{u} (Fin n) :=
  (Equiv.ofBijective (fun i : ULift.{u} (Fin n) ↦
    (⟨⟨i.down.succ⟩, by simp⟩ : {j : ULift.{u} (Fin (n + 1)) // j ≠ ⟨0⟩})) (by
      constructor
      · intro a b hab
        apply ULift.ext
        exact Fin.succ_injective _ (congrArg (fun j ↦ j.val.down) hab)
      · rintro ⟨⟨j⟩, hj⟩
        refine Fin.cases ?_ (fun k ↦ ?_) j hj
        · exact fun h ↦ False.elim (h rfl)
        · intro h
          exact ⟨⟨k⟩, rfl⟩)).symm
private noncomputable def affineCoordinateChart (S : Scheme.{u}) (n : ℕ) :
    AffineSpace (ULift.{u} (Fin n)) S ≅
      (standardOpen (ULift.{u} (Fin (n + 1))) S ⟨0⟩).toScheme :=
  AffineSpace.reindexIso S (coordinateIndex n) ≪≫
    (standardOpenIso (ULift.{u} (Fin (n + 1))) S ⟨0⟩).symm
private theorem affineCoordinateChart_over (S : Scheme.{u}) (n : ℕ) :
    (affineCoordinateChart S n).hom ≫
      (standardOpen (ULift.{u} (Fin (n + 1))) S ⟨0⟩).ι ≫
      (ℙ(ULift.{u} (Fin (n + 1)); S) ↘ S) =
        (AffineSpace (ULift.{u} (Fin n)) S ↘ S) := by
  simp only [affineCoordinateChart, Iso.trans_hom, Iso.symm_hom,
    AffineSpace.reindexIso_hom, Category.assoc, standardOpenIso_inv_ι_over,
    AffineSpace.reindex_over]
private theorem inverseChart_ratio (I : Type u) (S : Scheme.{u}) (i : I)
    (j : {j : I // j ≠ i}) :
    ((standardOpenIso I S i).inv ≫ (standardOpen I S i).ι).appLE
      (standardOpen I S i) ⊤ (by simp) (coordRatio I S i j) =
        AffineSpace.coord S j := by
  have hle : ⊤ ≤ homOfSections (AffineSpace {j : I // j ≠ i} S ↘ S)
      (coordOne S i) (span_range_coordOne S i) ⁻¹ᵁ standardOpen I S i := by
    rw [homOfSections_preimage_standardOpen, coordOne_self, Scheme.basicOpen_one]
  rw [Scheme.Hom.appLE_congr_hom (homOfSections_coord_eq S i).symm _ _ _ hle,
    homOfSections_appLE_coordRatio _ _ _ (coordOne_self S i), coordOne_of_ne]
private theorem affineCoordinateChart_ratios (S : Scheme.{u}) (n : ℕ) (i : Fin n) :
    ((affineCoordinateChart S n).hom ≫
      (standardOpen (ULift.{u} (Fin (n + 1))) S ⟨0⟩).ι).appLE
        (standardOpen (ULift.{u} (Fin (n + 1))) S ⟨0⟩) ⊤ (by simp)
        (coordRatio (ULift.{u} (Fin (n + 1))) S ⟨0⟩ ⟨i.succ⟩) =
          AffineSpace.coord S ⟨i⟩ := by
  let ψ := (standardOpenIso (ULift.{u} (Fin (n + 1))) S ⟨0⟩).inv ≫
    (standardOpen (ULift.{u} (Fin (n + 1))) S ⟨0⟩).ι
  have hψ : ⊤ ≤ ψ ⁻¹ᵁ standardOpen (ULift.{u} (Fin (n + 1))) S ⟨0⟩ := by
    simp [ψ, Scheme.Opens.ι_preimage_self]
  have hcomp : (affineCoordinateChart S n).hom ≫
      (standardOpen (ULift.{u} (Fin (n + 1))) S ⟨0⟩).ι =
      (AffineSpace.reindexIso S (coordinateIndex n)).hom ≫ ψ := rfl
  have hmap := Scheme.Hom.appLE_comp_appLE
    (AffineSpace.reindexIso S (coordinateIndex n)).hom ψ
    (standardOpen (ULift.{u} (Fin (n + 1))) S ⟨0⟩) ⊤ ⊤ hψ le_top
  rw [Scheme.Hom.appLE_congr_hom hcomp _ _ _ (by simp [top_unique hψ])]
  rw [← hmap, CommRingCat.comp_apply, Scheme.Hom.appLE_top_top]
  dsimp only [ψ]
  rw [inverseChart_ratio (ULift.{u} (Fin (n + 1))) S ⟨0⟩ ⟨⟨i.succ⟩, by simp⟩,
    AffineSpace.reindexIso_hom, AffineSpace.reindex_appTop_coord]
  congr 1
  exact (coordinateIndex n).apply_symm_apply ⟨i⟩
private theorem coordinatePoint_in_chart (S : Scheme.{u}) (n : ℕ)
    (x : (⨆ i : Fin n, Scheme.Modules.Hom.zeroLocus (coordinateSection
      (ULift.{u} (Fin (n + 1))) S ⟨i.succ⟩)).subscheme) :
    (⨆ i : Fin n, Scheme.Modules.Hom.zeroLocus (coordinateSection
      (ULift.{u} (Fin (n + 1))) S ⟨i.succ⟩)).subschemeι x ∈
      standardOpen (ULift.{u} (Fin (n + 1))) S ⟨0⟩ := by
  let D (i : Fin n) := Scheme.Modules.Hom.zeroLocus (coordinateSection
    (ULift.{u} (Fin (n + 1))) S ⟨i.succ⟩)
  let J := ⨆ i, D i
  let y := J.subschemeι x
  have hy : y ∈ J.support := by
    exact (Set.ext_iff.mp J.range_subschemeι y).mp ⟨x, rfl⟩
  obtain ⟨⟨j⟩, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_standardOpen (ULift.{u} (Fin (n + 1))) S).ge (show y ∈ ⊤ from trivial))
  rcases Fin.eq_zero_or_eq_succ j with h | ⟨i, rfl⟩
  · simpa only [h] using hj
  · have hmem : y ∈ (D i).support :=
      Scheme.IdealSheafData.support_antitone (le_iSup D i) hy
    have hnot : y ∉ (D i).support := by
      change y ∈ (D i).support.compl
      rw [compl_support_zeroLocus_coordinateSection]
      exact hj
    exact False.elim (hnot hmem)

private theorem point_ideal_chart (R : Type u) [CommRing R] (n : ℕ) :
    (⨆ i : Fin n, (coordinateSection (ULift.{u} (Fin (n + 1)))
      (Spec (.of R)) ⟨i.succ⟩).zeroLocus).ideal
        ⟨standardOpen _ (Spec (.of R)) ⟨0⟩, isAffineOpen_standardOpen _ _ _⟩ =
      (MvPolynomial.idealOfVars {j : ULift.{u} (Fin (n + 1)) // j ≠ ⟨0⟩} R).map
        (chartRingEquiv _ R ⟨0⟩).toRingHom := by
  let I := ULift.{u} (Fin (n + 1))
  let S := Spec (.of R)
  let U : (ℙ(I; S)).affineOpens :=
    ⟨standardOpen I S ⟨0⟩, isAffineOpen_standardOpen I S ⟨0⟩⟩
  have : SheafOfModules.IsInvertible.{u, u, u} (𝟙_ (ℙ(I; S)).Modules) :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ (ℙ(I; S)).Modules)
  have hid (i : Fin n) : (coordinateSection I S ⟨i.succ⟩).zeroLocus.ideal U =
      Ideal.span {coordRatio I S ⟨0⟩ ⟨i.succ⟩} :=
    Scheme.Modules.Hom.ideal_zeroLocus _ U
      (Scheme.Modules.isFreeGenerator_one (X := ℙ(I; S)) U.1)
      (isFreeGenerator_twistGenerator I S 1 ⟨0⟩)
      (coordinateSection_app_standardOpen I S ⟨i.succ⟩ ⟨0⟩)
  change (⨆ i : Fin n, (coordinateSection I S ⟨i.succ⟩).zeroLocus).ideal U = _
  rw [Scheme.IdealSheafData.ideal_iSup, iSup_apply]
  simp_rw [hid]
  rw [← Ideal.span_range_eq_iSup, MvPolynomial.idealOfVars, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨MvPolynomial.X ⟨⟨i.succ⟩, by simp⟩, ⟨⟨⟨i.succ⟩, by simp⟩, rfl⟩,
      chartRingEquiv_X I R (⟨0⟩ : I) ⟨⟨i.succ⟩, by simp [I]⟩⟩
  · rintro ⟨_, ⟨⟨⟨j⟩, hj⟩, rfl⟩, rfl⟩
    rcases Fin.eq_zero_or_eq_succ j with h | ⟨i, rfl⟩
    · exact False.elim (hj (congrArg ULift.up h))
    · exact ⟨i, (chartRingEquiv_X I R (⟨0⟩ : I) ⟨⟨i.succ⟩, hj⟩).symm⟩
private theorem coordinatePoint_isIso (R : Type u) [CommRing R] (n : ℕ) :
    IsIso ((⨆ i : Fin n, (coordinateSection (ULift.{u} (Fin (n + 1)))
      (Spec (.of R)) ⟨i.succ⟩).zeroLocus).subschemeι ≫
        (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R))) := by
  classical
  let I := ULift.{u} (Fin (n + 1))
  let S := Spec (.of R)
  let X := ℙ(I; S)
  let π : X ⟶ S := X ↘ S
  let U : X.affineOpens :=
    ⟨standardOpen I S ⟨0⟩, isAffineOpen_standardOpen I S ⟨0⟩⟩
  let J := ⨆ i : Fin n, (coordinateSection I S ⟨i.succ⟩).zeroLocus
  let V := {j : I // j ≠ ⟨0⟩}
  let E := chartRingEquiv I R ⟨0⟩
  have hJ : J.ideal U = (MvPolynomial.idealOfVars V R).map E.toRingHom :=
    point_ideal_chart R n
  let e := Ideal.quotientEquiv (MvPolynomial.idealOfVars V R) (J.ideal U) E hJ
  let c : R →+* Γ(X, U) ⧸ J.ideal U :=
    (Ideal.Quotient.mk (J.ideal U)).comp (π.specStructureMap U).hom
  have hc : Function.Bijective c := by
    have heq : e.toRingHom.comp
        ((Ideal.Quotient.mk (MvPolynomial.idealOfVars V R)).comp MvPolynomial.C) = c := by
      ext a
      change Ideal.Quotient.mk (J.ideal U) (E (MvPolynomial.C a)) = _
      rw [chartRingEquiv_C]
      rfl
    rw [← heq]
    exact e.bijective.comp (polynomial_constants_bijective V R)
  have : IsIso (CommRingCat.ofHom c) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hc
  have hcomp : J.subschemeCover.f U ≫ J.subschemeι ≫ π =
      Spec.map (CommRingCat.ofHom c) := by
    rw [← Category.assoc, J.subschemeCover_map_subschemeι,
      J.glueDataObjι_ι, Category.assoc, Scheme.Hom.fromSpec_comp_eq_specMap,
      ← Spec.map_comp]
    rfl
  have htop : (J.subschemeCover.f U).opensRange = ⊤ := by
    rw [J.opensRange_subschemeCover_map]
    ext x
    exact ⟨fun _ ↦ trivial, fun _ ↦ coordinatePoint_in_chart S n x⟩
  have : Surjective (J.subschemeCover.f U) := by
    rw [surjective_iff]
    intro x
    have hx : x ∈ (J.subschemeCover.f U).opensRange := by rw [htop]; trivial
    exact hx
  have : IsIso (J.subschemeCover.f U) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso (J.subschemeCover.f U ≫ (J.subschemeι ≫ π)) := by
    rw [hcomp]
    infer_instance
  exact (isIso_comp_left_iff (J.subschemeCover.f U) (J.subschemeι ≫ π)).mp inferInstance

/-- Field-coordinate geometry of the polynomial projective-space model.
Source: Stacks Project, Constructions, Tags 01NG and 01MS;
steps 10--13 of lem-pur-projective-bundle-tautological-geometry.
(blueprint: lem-pur-projective-bundle-coordinate-geometry).

Proof: setting T_0 to zero is a graded surjection to the polynomial algebra on
the remaining variables. Its Proj map is a closed immersion. On D_+(T_j), j not
zero, its kernel is the principal ideal (T_0/T_j), so its image is exactly the
scheme-theoretic zero locus of the coordinate section. Its source is P^{n-1}.
The complement is D_+(T_0), whose polynomial chart has the n coordinates T_i/T_0;
the standard chart isomorphism gives the specified AffineChart, including ratios.
For each i, on D_+(T_j) the equation of the coordinate divisor is T_i/T_j.
It is 1 when i=j, and otherwise a polynomial variable, hence a nonzerodivisor
by injectivity on monomial coefficients. This proves the Cartier assertion.
The dual generator to this local ideal has transition T_j/T_k, exactly the
transition of O(1); glue these isomorphisms to get the divisor line bundle.
Finally the sum of ideals for T_1,...,T_n is the unit ideal on each D_+(T_i)
with i nonzero. On D_+(T_0), its quotient is K[t_1,...,t_n]/(t_1,...,t_n)=K
by evaluation at zero, with inverse the constants. These descriptions identify
the whole intersection scheme with Spec K over K, prove it reduced, and show
it lies in the zeroth chart. For n=0 the intersection is the whole one-coordinate
projective space, canonically Spec K, and no hyperplane assertion is required. -/
theorem exists_projectiveBundleCoordinateGeometry (K : Type u) [Field K] (n : ℕ) :
    Nonempty (ProjectiveBundleCoordinateGeometry K n) := by
  classical
  obtain ⟨C⟩ := exists_projectiveBundleCoordinateSubschemes K n
  have := coordinatePoint_isIso K n
  exact ⟨{
    hyperplane := C.hyperplane
    hyperplane_over := C.hyperplane_over
    affine := affineCoordinateChart (Spec (.of K)) n
    affine_over := affineCoordinateChart_over (Spec (.of K)) n
    ratios := affineCoordinateChart_ratios (Spec (.of K)) n
    divisor := coordinate_divisor _ K
    divisorLineBundle := fun i ↦ Classical.choice (lineBundle_of_coordinate_divisor
      (coordinateSection _ (Spec (.of K)) i) (coordinate_divisor _ K i))
    point := asIso _
    point_over := rfl
    point_reduced := isReduced_of_isOpenImmersion
      ((⨆ i : Fin n, Scheme.Modules.Hom.zeroLocus (coordinateSection
        (ULift.{u} (Fin (n + 1))) (Spec (.of K)) ⟨i.succ⟩)).subschemeι ≫
          (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of K)) ↘ Spec (.of K)))
    point_in_chart := coordinatePoint_in_chart (Spec (.of K)) n }⟩

end AlgebraicGeometry
