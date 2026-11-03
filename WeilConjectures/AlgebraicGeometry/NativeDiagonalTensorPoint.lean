/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldRestrictionExteriorProduct
public import Mathlib.RingTheory.TensorProduct.Maps

import WeilConjectures.AlgebraicGeometry.FieldRestrictionExteriorProduct
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.AlgebraicGeometry.DerivedScalarRestrictionTensor
import WeilConjectures.Mathlib.CategoryTheory.Conj
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import all WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Category.Ring.FilteredColimits
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # The diagonal retract of the native point tensor

This is the point case of the termwise separability argument in the first paragraph of
`lem-pur-ordinary-kunneth-finite-ring.proof.md`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Etale
open scoped ModuleCat.Algebra

section Localization
variable {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
  [Abelian C] [Abelian D] [IsGrothendieckAbelian.{u + 1} C]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D]
  [MonoidalClosed C] [MonoidalClosed D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (ordinary : G.LaxMonoidal) (t : RestrictionTensorData G ordinary)
  (K L : CochainComplex C ℤ)

private theorem tensorLocalizationConjugate_map
    [IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((G.mapHomologicalComplex (.up ℤ)).obj K)
      ((G.mapHomologicalComplex (.up ℤ)).obj L))]
    (f : K ⟶ K) (g : L ⟶ L) :
    let i := tensorIso (G.mapDerivedCategoryFactors.app K)
        (G.mapDerivedCategoryFactors.app L) ≪≫
      asIso (Functor.LaxMonoidal.μ DerivedCategory.Q
        ((G.mapHomologicalComplex (.up ℤ)).obj K)
        ((G.mapHomologicalComplex (.up ℤ)).obj L))
    i.hom ≫ DerivedCategory.Q.map
        ((G.mapHomologicalComplex (.up ℤ)).map f ⊗ₘ
          (G.mapHomologicalComplex (.up ℤ)).map g) ≫ i.inv =
      G.mapDerivedCategory.map (DerivedCategory.Q.map f) ⊗ₘ
        G.mapDerivedCategory.map (DerivedCategory.Q.map g) := by
  let i := tensorIso (G.mapDerivedCategoryFactors.app K)
      (G.mapDerivedCategoryFactors.app L) ≪≫
    asIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((G.mapHomologicalComplex (.up ℤ)).obj K)
      ((G.mapHomologicalComplex (.up ℤ)).obj L))
  change i.hom ≫ _ ≫ i.inv = _
  apply (cancel_mono i.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [i, Iso.trans_hom, tensorIso_hom, Iso.app_hom, asIso_hom]
  simp only [Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  simp only [tensorIso_hom, Iso.app_hom, tensorHom_comp_tensorHom]
  congr 1
  · exact (G.mapDerivedCategoryFactors.hom.naturality f).symm
  · exact (G.mapDerivedCategoryFactors.hom.naturality g).symm


end Localization


/-- The normalized balanced point tensor and its diagonal section.
Source: finite-ring Kunneth proof, first paragraph, point case.
(blueprint: lem-pur-native-diagonal-tensor-point). -/
structure NativeDiagonalTensorPointData
    (F B : Type (u + 1)) [Field F] [Field B] [Algebra F B]
    (e : B ⊗[F] B)
    (t : RestrictionTensorData (ModuleCat.restrictScalars (algebraMap F B)) inferInstance)
    (M N : DerivedCategory (ModuleCat.{u + 1} B)) where
  action : (B ⊗[F] B) →+* End
    ((ModuleCat.restrictScalars (algebraMap F B)).mapDerivedCategory.obj M ⊗
      (ModuleCat.restrictScalars (algebraMap F B)).mapDerivedCategory.obj N)
  action_pure : ∀ a b : B, action (a ⊗ₜ[F] b) =
    (ModuleCat.restrictScalars (algebraMap F B)).mapDerivedCategory.map (a • 𝟙 M) ⊗ₘ
      (ModuleCat.restrictScalars (algebraMap F B)).mapDerivedCategory.map (b • 𝟙 N)
  inclusion : (ModuleCat.restrictScalars (algebraMap F B)).mapDerivedCategory.obj (M ⊗ N) ⟶
    (ModuleCat.restrictScalars (algebraMap F B)).mapDerivedCategory.obj M ⊗
      (ModuleCat.restrictScalars (algebraMap F B)).mapDerivedCategory.obj N
  split : inclusion ≫ t.map M N = 𝟙 _
  retract : t.map M N ≫ inclusion = action e

/-- Finite separability splits the normalized native point tensorator.
Source: the first paragraph of the finite-ring Kunneth proof.

Proof. Write the separability element as a finite sum of pure tensors. The section of the
ordinary balanced quotient sends x tensor_B y to the sum of a_i x tensor_F b_i y.
The diagonal annihilation relation makes this B-balanced. Multiplication(e)=1 proves
section followed by quotient is the identity; the reverse composite is the e-action.
Apply these maps to every bidegree of the direct-sum tensor total complex. The maps commute
with the differentials and are natural. Complexes of vector spaces are K-flat, before and
after restriction. Descend the two maps through localization and transport through the
standard derived tensor comparisons. The chain_summand and normalization clauses of t
identify its map with the descended quotient. The pure-action equation follows from the
same total-summand calculation for coefficient multiplication. All formulas apply also to
zero or unbounded complexes.
(blueprint: lem-pur-native-diagonal-tensor-point). -/
theorem nativeDiagonalTensorPoint
    (F B : Type (u + 1)) [Field F] [Field B] [Finite F] [Finite B] [Algebra F B]
    (e : B ⊗[F] B) (hμ : Algebra.TensorProduct.lmul' F e = 1)
    (hd : ∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0)
    (t : RestrictionTensorData (ModuleCat.restrictScalars (algebraMap F B)) inferInstance)
    (M N : DerivedCategory (ModuleCat.{u + 1} B)) :
    Nonempty (NativeDiagonalTensorPointData F B e t M N) := by
  let G := ModuleCat.restrictScalars.{u + 1} (algebraMap F B)
  let K := DerivedCategory.Q.objPreimage M
  let L := DerivedCategory.Q.objPreimage N
  let m : DerivedCategory.Q.obj K ≅ M := DerivedCategory.Q.objObjPreimageIso M
  let n : DerivedCategory.Q.obj L ≅ N := DerivedCategory.Q.objObjPreimageIso N
  obtain ⟨a, s, hs, hp, ha⟩ := nativePointChainRetraction F B e hμ hd t K L
  have := tensorComparisonIsoOfAllFlat
    (fun X : ModuleCat.{u + 1} B ↦ (ModuleCat.flat_iff_flat X).2 inferInstance) K L
  have := tensorComparisonIsoOfAllFlat
    (fun X : ModuleCat.{u + 1} F ↦ (ModuleCat.flat_iff_flat X).2 inferInstance)
    ((G.mapHomologicalComplex (.up ℤ)).obj K)
    ((G.mapHomologicalComplex (.up ℤ)).obj L)
  obtain ⟨ad, sd, hsd, hpd, had⟩ := diagonalTensorLocalization G inferInstance t K L
    a s e hs hp
  have hadp (b c : B) : ad (b ⊗ₜ[F] c) =
      G.mapDerivedCategory.map (b • 𝟙 (DerivedCategory.Q.obj K)) ⊗ₘ
        G.mapDerivedCategory.map (c • 𝟙 (DerivedCategory.Q.obj L)) := by
    rw [had, ha]
    have h := tensorLocalizationConjugate_map G K L (b • 𝟙 K) (c • 𝟙 L)
    have hK : DerivedCategory.Q.map (b • 𝟙 K) =
        b • 𝟙 (DerivedCategory.Q.obj K) := by rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    have hL : DerivedCategory.Q.map (c • 𝟙 L) =
        c • 𝟙 (DerivedCategory.Q.obj L) := by rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    rw [hK, hL] at h
    dsimp only [G] at h ⊢
    simpa only [Iso.trans_hom, Iso.trans_inv, tensorIso_hom, tensorIso_inv,
      Iso.app_hom, Iso.app_inv, asIso_hom, asIso_inv, Category.assoc] using h
  let i := tensorIso (G.mapDerivedCategory.mapIso m) (G.mapDerivedCategory.mapIso n)
  let j := G.mapDerivedCategory.mapIso (tensorIso m n)
  let af := i.conjRingEquiv.toRingHom.comp ad
  let sf := j.inv ≫ sd ≫ i.hom
  have ht : t.map M N = i.inv ≫ t.map (DerivedCategory.Q.obj K)
      (DerivedCategory.Q.obj L) ≫ j.hom := by
    apply (cancel_epi i.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    simpa only [i, j, tensorIso_hom, Functor.mapIso_hom, Category.assoc] using
      t.naturality m.hom n.hom
  refine ⟨{
    action := af
    action_pure := ?_
    inclusion := sf
    split := ?_
    retract := ?_ }⟩
  · intro b c
    change i.inv ≫ ad (b ⊗ₜ[F] c) ≫ i.hom = _
    rw [hadp]
    simp only [i, tensorIso_inv, tensorIso_hom, Functor.mapIso_inv,
      Functor.mapIso_hom, tensorHom_comp_tensorHom,
      ← G.mapDerivedCategory.map_comp]
    simp [Linear.smul_comp, Linear.comp_smul]
    rfl
  · rw [ht]
    simp only [sf, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc sd, hsd, Category.id_comp, Iso.inv_hom_id]
  · rw [ht]
    simp only [sf, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (t.map (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)), hpd]
    rfl


#print axioms nativeDiagonalTensorPoint

end AlgebraicGeometry.Etale
