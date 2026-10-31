/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTowerSupplement
import all WeilConjectures.Algebra.Homology.SuccessiveQuotientFlatTensorSequence
import Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.AlgebraicGeometry.AdicReductionTriangle
/-! # Self-reduction along a regular quotient of coefficient sheaves -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme


private local instance restriction_faithful
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) : (pbcRestrict φ).Faithful where
  map_injective := by
    intro M N f g h
    ext U x
    exact congrArg (fun k ↦ k.val.app U x) h

private theorem full_restriction_of_unit_epi
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (p : SheafOfModules.unit ((adicLisseForget T).obj R) ⟶
      (pbcRestrict φ).obj (SheafOfModules.unit ((adicLisseForget T).obj S))) [Epi p]
    (hp : ∀ U : T.ProEtᵒᵖ, p.val.app U (1 : R.obj.obj U) = (1 : S.obj.obj U)) :
    (pbcRestrict φ).Full := by
  let F := SheafOfModules.toSheaf ((adicLisseForget T).obj R)
  have : Epi (F.map p) := inferInstance
  have hsurj : Presheaf.IsLocallySurjective (ProEt.topology T) (F.map p).hom :=
    (Sheaf.isLocallySurjective_iff_epi' _ (F.map p)).2 inferInstance
  have hform (U : T.ProEtᵒᵖ) (x : R.obj.obj U) :
      p.val.app U x = φ.hom.app U x := by
    have h := (p.val.app U).hom.map_smul x (1 : R.obj.obj U)
    change (p.val.app U (x * (1 : R.obj.obj U)) : S.obj.obj U) =
      φ.hom.app U x * (@id (S.obj.obj U) (p.val.app U (1 : R.obj.obj U))) at h
    simpa only [mul_one, hp U, id_eq] using h
  have : Presheaf.IsLocallySurjective (ProEt.topology T)
      ((adicLisseForget T).map φ).hom := by
    constructor
    intro U s
    apply (ProEt.topology T).superset_covering _ (Presheaf.imageSieve_mem _ (F.map p).hom s)
    intro V f hf
    obtain ⟨x, hx⟩ := hf
    exact ⟨x, (hform (op V) x).symm.trans hx⟩
  exact SheafOfModules.restriction_full ((adicLisseForget T).map φ)



/-- Derived reduction of a module already over a regular principal quotient has that
module as its cohomology in degrees zero and minus one, and vanishes elsewhere.

Source: blueprint order 1429, counterexample in the levelwise-truncation proposition;
Stacks Project, Tag 06YU.
(blueprint: lem-weil-pbc-regular-quotient-self-cohomology).

Proof: the normalized unit quotient sequence gives a distinguished tensor triangle.
Its first map acts by the generator, which is zero on every quotient module. The
single complex has cohomology only in degree zero. The long exact sequence therefore
identifies degree zero through the unit and degree minus one through the boundary,
and forces all other degrees to vanish. Restriction along the quotient is exact,
faithful and full: the normalized epimorphism of units makes the coefficient map
locally surjective, so every linear map of restricted modules is quotient-linear.
Thus the two cohomology identifications lift to the quotient coefficient category.
No splitting of the derived object as a quotient-linear complex is asserted. -/
theorem regularQuotient_single_cohomology
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S)
    (f : SheafOfModules.unit ((adicLisseForget T).obj R) ⟶
      SheafOfModules.unit ((adicLisseForget T).obj R))
    (p : SheafOfModules.unit ((adicLisseForget T).obj R) ⟶
      (pbcRestrict φ).obj (SheafOfModules.unit ((adicLisseForget T).obj S)))
    (hp : ∀ U : T.ProEtᵒᵖ, p.val.app U (1 : R.obj.obj U) = (1 : S.obj.obj U))
    (hz : f ≫ p = 0) (hs : (ShortComplex.mk f p hz).ShortExact)
    (N : pbcModules T S) :
    let K := (pbcDerivedExtend φ).obj
      ((DerivedCategory.singleFunctor _ 0).obj ((pbcRestrict φ).obj N))
    Nonempty ((DerivedCategory.homologyFunctor _ 0).obj K ≅ N) ∧
    Nonempty ((DerivedCategory.homologyFunctor _ (-1)).obj K ≅ N) ∧
    ∀ q : ℤ, q ≠ 0 → q ≠ -1 → IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
  have : Epi p := hs.epi_g
  let := full_restriction_of_unit_epi T φ p hp
  let M := (pbcRestrict φ).obj N
  let L := (DerivedCategory.singleFunctor _ 0).obj M
  let K := (pbcDerivedExtend φ).obj L
  let e₀ := (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M
  have hform (U : T.ProEtᵒᵖ) (x : R.obj.obj U) :
      p.val.app U x = φ.hom.app U x := by
    have h := (p.val.app U).hom.map_smul x (1 : R.obj.obj U)
    change (p.val.app U (x * (1 : R.obj.obj U)) : S.obj.obj U) =
      φ.hom.app U x * (@id (S.obj.obj U) (p.val.app U (1 : R.obj.obj U))) at h
    simpa only [mul_one, hp U, id_eq] using h
  have hscalar (U : T.ProEtᵒᵖ) :
      φ.hom.app U (f.val.app U (1 : R.obj.obj U)) = 0 := by
    have h := congrArg (fun k ↦ k.val.app U (1 : R.obj.obj U)) hz
    change p.val.app U (f.val.app U (1 : R.obj.obj U)) = 0 at h
    rw [hform] at h
    exact h
  let α := ReductionTensor.multiplicationNatural T R f
  have hμ : α.app M = 0 := by
    ext U x
    change (ReductionTensor.tensorMultiplication T R f M).val.app U x = 0
    rw [ReductionTensor.tensorMultiplication_apply]
    change φ.hom.app U (f.val.app U (1 : R.obj.obj U)) •
      (@id (N.val.obj U) x) = 0
    rw [hscalar, zero_smul]
  have hα (q : ℤ) : α.app ((DerivedCategory.homologyFunctor _ q).obj L) = 0 := by
    by_cases hq : q = 0
    · subst q
      apply (cancel_mono e₀.hom).1
      have h := α.naturality e₀.hom
      change e₀.hom ≫ α.app M =
        α.app ((DerivedCategory.homologyFunctor _ 0).obj L) ≫ e₀.hom at h
      rw [hμ, comp_zero] at h
      simpa only [zero_comp] using h.symm
    · have hzero : IsZero ((DerivedCategory.homologyFunctor _ q).obj L) := by
        by_cases h : q < 0
        · exact DerivedCategory.isZero_of_isGE L 0 q h
        · exact DerivedCategory.isZero_of_isLE L 0 q (by omega)
      exact hzero.eq_of_src _ _
  obtain ⟨a,w,ht,hcoh⟩ := pbc_adic_reduction_triangle T φ f p hp hz hs L
  let tr := Pretriangulated.Triangle.mk a ((pbcDerivedScalarAdjunction φ).unit.app L) w
  have ha (q : ℤ) : (DerivedCategory.homologyFunctor _ q).map a = 0 := by
    let H := (DerivedCategory.homologyFunctor _ q).obj L
    let eH := ReductionTensor.tensorUnitIso T R H
    have hF : (SheafOfModules.siteSheafTensorRight
        (J := ProEt.topology T) (A := R) H).map f = 0 := by
      apply (cancel_epi eH.inv).1
      apply (cancel_mono eH.hom).1
      have hh := hα q
      change eH.inv ≫ _ ≫ eH.hom = 0 at hh
      simpa only [Category.assoc, comp_zero, zero_comp] using hh
    obtain ⟨e,he⟩ := (hcoh q).1
    apply (cancel_mono e.hom).1
    dsimp only [H] at hF
    rw [hF, comp_zero] at he
    simpa only [zero_comp] using he
  have hL (q : ℤ) (hq : q ≠ 0) : IsZero ((DerivedCategory.homologyFunctor _ q).obj L) := by
    by_cases h : q < 0
    · exact DerivedCategory.isZero_of_isGE L 0 q h
    · exact DerivedCategory.isZero_of_isLE L 0 q (by omega)
  have : Mono ((DerivedCategory.homologyFunctor _ 0).map tr.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff tr ht 0).2 (ha 0)
  have : Epi ((DerivedCategory.homologyFunctor _ 0).map tr.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff tr ht 0 1 rfl).2
      ((hL 1 (by omega)).eq_of_tgt _ _)
  have : IsIso ((DerivedCategory.homologyFunctor _ 0).map tr.mor₂) :=
    isIso_of_mono_of_epi _
  let δ := DerivedCategory.HomologySequence.δ tr (-1) 0 (by omega)
  have : Mono δ := (DerivedCategory.HomologySequence.exact₃ tr ht (-1) 0 (by omega)).mono_g
    ((hL (-1) (by omega)).eq_of_src _ _)
  have : Epi δ := (DerivedCategory.HomologySequence.exact₁ tr ht (-1) 0 (by omega)).epi_f
    (ha 0)
  have : IsIso δ := isIso_of_mono_of_epi _
  let c₀ := ((pbcRestrict φ).mapDerivedCategoryHomologyFunctorIso 0).app K
  let cm := ((pbcRestrict φ).mapDerivedCategoryHomologyFunctorIso (-1)).app K
  refine ⟨⟨(pbcRestrict φ).preimageIso
      (c₀ ≪≫ (asIso ((DerivedCategory.homologyFunctor _ 0).map tr.mor₂)).symm ≪≫ e₀)⟩,
    ⟨(pbcRestrict φ).preimageIso (cm ≪≫ asIso δ ≪≫ e₀)⟩, ?_⟩
  intro q hq hq'
  have hex := DerivedCategory.HomologySequence.exact₃ tr ht q (q+1) rfl
  have hzero := hex.isZero_of_both_isZero (hL q hq) (hL (q+1) (by omega))
  have hU : IsZero ((pbcRestrict φ).obj ((DerivedCategory.homologyFunctor _ q).obj K)) :=
    hzero.of_iso (((pbcRestrict φ).mapDerivedCategoryHomologyFunctorIso q).app K)
  apply (IsZero.iff_id_eq_zero _).2
  apply (pbcRestrict φ).map_injective
  simpa only [Functor.map_id, Functor.map_zero] using
    hU.eq_of_src ((pbcRestrict φ).map (𝟙 _)) ((pbcRestrict φ).map (0 : _ ⟶ _))

end AlgebraicGeometry.Scheme
