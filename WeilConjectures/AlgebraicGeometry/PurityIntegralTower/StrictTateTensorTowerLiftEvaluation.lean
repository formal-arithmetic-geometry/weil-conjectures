/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.CondensedTateIntegralTowerData
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! Evaluation identity for strict ordinary Tate quotient towers.

Source: smooth-purity transport, normalized Tate tower, Steps 2--3.
(blueprint: lem-pur-strict-tate-tensor-tower-evaluation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory

private lemma coefficientLift_projection (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (n : ℕ) :
    pbcCompletedScalar T (datum.{u} ell) ≫ pbcAdicProjection T (datum.{u} ell) n =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk ((datum.{u} ell).ideal ^ (n + 1)))) ≫
          (pbcLevelConstantComparison T (datum.{u} ell) n).hom := by
  dsimp only [pbcCompletedScalar, pbcAdicProjection, pbcCompletedComparison]
  rw [Category.assoc]
  erw [HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc]
  erw [(adicDatumScalar_exists T
    { toCompleteCoefficientDatum := (datum.{u} ell).toCompleteCoefficientDatum,
      quotientFinite := (datum.{u} ell).quotientFinite }).exists.choose_spec n]
  rfl

private lemma projection_locallySurjective (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (n : ℕ) :
    Presheaf.IsLocallySurjective (ProEt.topology T)
      ((adicLisseForget T).map (pbcAdicProjection T (datum.{u} ell) n)).hom := by
  let J := ProEt.topology T
  let A := CommRingCat.of (Ring.{u} ell)
  let B := CommRingCat.of (Ring.{u} ell ⧸ (datum.{u} ell).ideal ^ (n + 1))
  let f : A ⟶ B := CommRingCat.ofHom (Ideal.Quotient.mk _)
  let ηA := toSheafify J ((Functor.const T.ProEtᵒᵖ).obj A)
  let ηB := toSheafify J ((Functor.const T.ProEtᵒᵖ).obj B)
  let g := (Functor.const T.ProEtᵒᵖ).map f
  have : Presheaf.IsLocallySurjective J g :=
    Presheaf.isLocallySurjective_of_surjective J g (fun _ ↦ Ideal.Quotient.mk_surjective)
  let e := (pbcLevelConstantComparison T (datum.{u} ell) n).hom
  have : Presheaf.IsLocallySurjective J (g ≫ ηB ≫ e.hom) := by infer_instance
  have hf : ηA ≫ (pbcCompletedScalar T (datum.{u} ell)).hom ≫
      (pbcAdicProjection T (datum.{u} ell) n).hom = g ≫ ηB ≫ e.hom := by
    change ηA ≫ (pbcCompletedScalar T (datum.{u} ell) ≫
      pbcAdicProjection T (datum.{u} ell) n).hom = _
    rw [coefficientLift_projection]
    change ηA ≫ (sheafifyMap J g) ≫ e.hom = _
    rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  have : Presheaf.IsLocallySurjective J
      ((pbcCompletedScalar T (datum.{u} ell)).hom ≫ (pbcAdicProjection T (datum.{u} ell) n).hom) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hf
  have hp := Presheaf.isLocallySurjective_of_isLocallySurjective J
    (pbcCompletedScalar T (datum.{u} ell)).hom (pbcAdicProjection T (datum.{u} ell) n).hom
  exact ⟨fun {U} s ↦ hp.imageSieve_mem s⟩

private lemma restriction_full (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    (pbcRestrict (pbcAdicProjection T (datum.{u} ell) n)).Full := by
  let f := (adicLisseForget T).map (pbcAdicProjection T (datum.{u} ell) n)
  let := projection_locallySurjective T ell n
  refine ⟨fun {M N} g ↦ ?_⟩
  let e := PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    (J := ProEt.topology T) (M₁ := M.val) f.hom N.isSheaf
  refine ⟨⟨e.symm g.val⟩, ?_⟩
  apply SheafOfModules.hom_ext
  exact e.apply_symm_apply g.val

private lemma restriction_faithful (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    (pbcRestrict (pbcAdicProjection T (datum.{u} ell) n)).Faithful where
  map_injective {M N} f g h := by
    ext U x
    exact congrArg (fun k ↦ k.val.app U x) h

end AlgebraicGeometry.Scheme.PurityIntegralTower
