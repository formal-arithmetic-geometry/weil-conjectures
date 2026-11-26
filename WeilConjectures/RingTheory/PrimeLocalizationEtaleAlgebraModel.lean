/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.EtaleAlgebraFilteredColimitDescent
import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.BaseChange

/-! # Unpointed affine étale descent at a prime

An étale algebra over `R_p` comes from an étale `R`-algebra by localization.

## Implementation details

The statement has no field, prime over `p` or residue-field pointing; those data and all
pointing identities are constructed by the caller.

## References

* [Stacks, Tag 00U2] (parts (9) and (10))
* [Stacks, Tag 00CR] and [Stacks, Tag 00CP]
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- An étale algebra over R_p comes from an étale R-algebra by localization. -/
theorem primeLocalization_etale_algebra_model
    (R : CommRingCat.{u}) (p : Spec R) (B : CommRingCat.{u})
    (α : CommRingCat.of (Localization.AtPrime p.asIdeal) ⟶ B)
    (hα : Etale (Spec.map α)) :
    ∃ (C : CommRingCat.{u}) (a : R ⟶ C) (i : C ⟶ B),
      Etale (Spec.map a) ∧
      a ≫ i = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ α ∧
      ∃ M : Submonoid C, (letI := i.hom.toAlgebra; IsLocalization M B) := by
  classical
  let F := CommRingCat.awayProdDiagram p.asIdeal
  let c := CommRingCat.awayProdCocone p.asIdeal
  have hc : CategoryTheory.Limits.IsColimit c := CommRingCat.isColimitAwayProdCocone p.asIdeal
  let E : CategoryTheory.Limits.colimit F ≅ c.pt :=
    (CategoryTheory.Limits.colimit.isColimit F).coconePointUniqueUpToIso hc
  let f : CategoryTheory.Limits.colimit F ⟶ B := E.hom ≫ α
  have hf : Etale (Spec.map f) := by
    have := hα
    dsimp [f]
    rw [Spec.map_comp]
    infer_instance
  obtain ⟨s, C, hC, g, hg, ⟨e⟩⟩ :=
    exists_etale_algebra_of_filteredColimit F B f hf
  let A : Type u := (CategoryTheory.Limits.colimit F : CommRingCat.{u})
  let S : Type u := CommRingCat.AwayProd p.asIdeal s
  let : Algebra S A := (CategoryTheory.Limits.colimit.ι F s).hom.toAlgebra
  let : Algebra S C := g.hom.toAlgebra
  let : Algebra A B := f.hom.toAlgebra
  let T := TensorProduct S A C
  let i : CommRingCat.of C ⟶ B :=
    CommRingCat.ofHom (e.symm.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := S) (A := A) (B := C)).toRingHom)
  let a : R ⟶ CommRingCat.of C := CommRingCat.ofHom (algebraMap R S) ≫ g
  have ha : Etale (Spec.map a) := by
    have := hg
    have : Algebra.Etale R S := Algebra.Etale.of_isLocalizationAway (∏ x ∈ s, (x : R))
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
    dsimp [a]
    rw [Spec.map_comp]
    infer_instance
  have hgi : g ≫ i = CategoryTheory.Limits.colimit.ι F s ≫ f := by
    ext x
    change e.symm (TensorProduct.tmul S 1 (algebraMap S C x)) = _
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    exact e.symm.commutes ((CategoryTheory.Limits.colimit.ι F s).hom x)
  refine ⟨CommRingCat.of C, a, i, ha, ?_, ?_⟩
  · change (CommRingCat.ofHom (algebraMap R S) ≫ g) ≫ i = _
    rw [Category.assoc, hgi]
    have HE : CategoryTheory.Limits.colimit.ι F s ≫ E.hom = c.ι.app s :=
      (CategoryTheory.Limits.colimit.isColimit F).comp_coconePointUniqueUpToIso_hom hc s
    change CommRingCat.ofHom (algebraMap R S) ≫
      CategoryTheory.Limits.colimit.ι F s ≫ E.hom ≫ α = _
    rw [← Category.assoc (CategoryTheory.Limits.colimit.ι F s), HE, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ α)
      (CommRingCat.ofHom_algebraMap_comp_awayProdCocone_ι_app p.asIdeal s)
  · let : Algebra R A :=
      (E.inv.hom.comp (algebraMap R (Localization.AtPrime p.asIdeal))).toAlgebra
    have : IsLocalization p.asIdeal.primeCompl A :=
      (IsLocalization.isLocalization_iff_of_ringEquiv
        (S := Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl
        (E.symm.commRingCatIsoToRingEquiv :
          Localization.AtPrime p.asIdeal ≃+* A)).mp inferInstance
    have : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      change E.inv.hom (algebraMap R (Localization.AtPrime p.asIdeal) x) =
        (CategoryTheory.Limits.colimit.ι F s).hom (algebraMap R S x)
      have H := congrArg (fun k ↦ k.hom (algebraMap R S x))
        ((CategoryTheory.Limits.colimit.isColimit F).comp_coconePointUniqueUpToIso_hom hc s)
      apply (ConcreteCategory.bijective_of_isIso E.hom).injective
      change E.hom.hom (E.inv.hom _) = E.hom.hom ((CategoryTheory.Limits.colimit.ι F s).hom _)
      rw [← CommRingCat.comp_apply, E.inv_hom_id]
      have Hc : (c.ι.app s).hom (algebraMap R S x) =
          algebraMap R (Localization.AtPrime p.asIdeal) x :=
        (CommRingCat.awayProdToAtPrime p.asIdeal s).commutes x
      exact Hc.symm.trans H.symm)
    have hle : Submonoid.powers (∏ x ∈ s, (x : R)) ≤ p.asIdeal.primeCompl := by
      apply Submonoid.powers_le.mpr
      exact Submonoid.prod_mem _ (fun x _ ↦ x.property)
    have : IsLocalization (p.asIdeal.primeCompl.map (algebraMap R S)) A :=
      IsLocalization.isLocalization_of_submonoid_le S A _ _ hle
    let : Algebra C T := Algebra.TensorProduct.rightAlgebra
    let M := Algebra.algebraMapSubmonoid C
      (p.asIdeal.primeCompl.map (algebraMap R S))
    have : IsLocalization M T := IsLocalization.tensorRight (S := C) (A := A) _
    refine ⟨M, ?_⟩
    exact (IsLocalization.isLocalization_iff_of_ringEquiv (R := C) (S := T)
      M (e.symm.toRingEquiv : T ≃+* B)).mp inferInstance

end AlgebraicGeometry.Scheme
