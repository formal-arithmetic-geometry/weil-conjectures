/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedTateIntegralTowerData
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

private lemma align_single
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Full] [F.Faithful] (i : ℤ) {K : DerivedCategory A} {L : A}
    {Y : DerivedCategory B} (q : K ≅ (_root_.DerivedCategory.singleFunctor A i).obj L)
    (e : F.mapDerivedCategory.obj K ≅ Y)
    (c : F.mapDerivedCategory.obj ((_root_.DerivedCategory.singleFunctor A i).obj L) ≅ Y) :
    ∃ r : K ≅ (_root_.DerivedCategory.singleFunctor A i).obj L,
      F.mapDerivedCategory.map r.inv ≫ e.hom = c.hom := by
  let H := _root_.DerivedCategory.singleFunctor A i ⋙ F.mapDerivedCategory
  let : H.Full := Functor.Full.of_iso (F.mapDerivedCategorySingleFunctor i).symm
  let : H.Faithful := Functor.Faithful.of_iso (F.mapDerivedCategorySingleFunctor i).symm
  let b : H.obj L ≅ H.obj L := F.mapDerivedCategory.mapIso q.symm ≪≫ e ≪≫ c.symm
  let a : L ≅ L := H.preimageIso b
  have ha : H.map a.inv = b.inv := H.map_preimage _
  refine ⟨q ≪≫ (_root_.DerivedCategory.singleFunctor A i).mapIso a, ?_⟩
  change F.mapDerivedCategory.map
      ((_root_.DerivedCategory.singleFunctor A i).map a.inv ≫ q.inv) ≫ e.hom = _
  rw [Functor.map_comp, Category.assoc]
  change H.map a.inv ≫ F.mapDerivedCategory.map q.inv ≫ e.hom = _
  rw [ha]
  simp only [b, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id, Category.comp_id]

/-- Choose level identifications of a strict Tate quotient tower that satisfy the
exact restriction/evaluation comparison displayed in the lift theorem.

Proof source: current blueprint, sec-smooth-purity/sk-thm-purity-transport,
Steps 2--3. Each completed-coefficient projection is locally surjective: lift a
local constant quotient section to the original coefficient ring, then map its
compatible residues into the completion. Ordinary scalar restriction is therefore
fully faithful. Full faithfulness of the single-complex functor and its exact
restriction comparison lift the discrepancy between the given evaluation and the
canonical single/evaluation comparison to an automorphism of the quotient line.
Compose the given level isomorphism with this automorphism. Its inverse cancels
the discrepancy, giving the required equality. The identifications are chosen
here; the equality does not hold for arbitrary initial identifications.
(blueprint: lem-pur-strict-tate-tensor-tower-evaluation)
-/
theorem strictTateTensorTower_evaluation
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (_hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ)
    (M : AdicTower T (datum.{u} ell))
    (q : ∀ n : ℕ, M.level n ≅
      (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).obj
        (quotientLine T ell n d))
    (h : M.tower = strictDerivedTower T ell d) :
    ∃ q' : ∀ n : ℕ, M.level n ≅
        (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).obj
          (quotientLine T ell n d),
      ∀ n : ℕ,
        (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) n)).map (q' n).inv ≫
          (M.evaluation n).hom ≫
          (pbcTowerEvaluation T (pbcAdicCompletion T (datum.{u} ell)) n).map
            (eqToHom h) =
        (Functor.mapDerivedCategorySingleFunctor
          (pbcRestrict (pbcAdicProjection T (datum.{u} ell) n))
          (-(2 * (d : ℤ)))).hom.app (quotientLine T ell n d) ≫
        (Functor.mapDerivedCategorySingleFunctor
          ((CategoryTheory.evaluation ℕᵒᵖ
            (pbcModules T (pbcAdicCompletion T (datum.{u} ell)))).obj (op n))
          (-(2 * (d : ℤ)))).inv.app (strictTower T ell d) := by
  classical
  have hn (n : ℕ) : ∃ r : M.level n ≅
      (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).obj
        (quotientLine T ell n d),
      (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) n)).map r.inv ≫
          (M.evaluation n).hom ≫
          (pbcTowerEvaluation T (pbcAdicCompletion T (datum.{u} ell)) n).map
            (eqToHom h) =
        (Functor.mapDerivedCategorySingleFunctor
          (pbcRestrict (pbcAdicProjection T (datum.{u} ell) n))
          (-(2 * (d : ℤ)))).hom.app (quotientLine T ell n d) ≫
        (Functor.mapDerivedCategorySingleFunctor
          ((CategoryTheory.evaluation ℕᵒᵖ
            (pbcModules T (pbcAdicCompletion T (datum.{u} ell)))).obj (op n))
          (-(2 * (d : ℤ)))).inv.app (strictTower T ell d) := by
    let R := pbcRestrict (pbcAdicProjection T (datum.{u} ell) n)
    let E := (CategoryTheory.evaluation ℕᵒᵖ
      (pbcModules T (pbcAdicCompletion T (datum.{u} ell)))).obj (op n)
    let : R.Full := restriction_full T ell n
    let : R.Faithful := restriction_faithful T ell n
    let c := (R.mapDerivedCategorySingleFunctor (-(2 * (d : ℤ)))).app
        (quotientLine T ell n d) ≪≫
      (E.mapDerivedCategorySingleFunctor (-(2 * (d : ℤ)))).symm.app (strictTower T ell d)
    obtain ⟨r, hr⟩ := align_single R (-(2 * (d : ℤ))) (q n)
      (M.evaluation n ≪≫ E.mapDerivedCategory.mapIso (eqToIso h)) c
    exact ⟨r, hr⟩
  choose q' hq' using hn
  exact ⟨q', hq'⟩

end AlgebraicGeometry.Scheme.PurityIntegralTower
