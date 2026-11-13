/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawDiagram
public import WeilConjectures.AlgebraicGeometry.RestrictedOverAbelianComplexData
import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomComparison
import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyNaturalIso
@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
/-- The nonnegative-degree scalar-forgetting comparison is natural for the fixed
five-factor pullback, with no affineness, qcqs, or limit hypotheses. -/
theorem exists_rawModule_restrictedAbelian_nonnegative
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale) :
    ∃ e : ∀ A : Over W,
      (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op A) ≅
        restrictedOverCohomology k
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)
          (q : ℤ) A U,
      ∀ (A B : Over W) (f : A ⟶ B),
        (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op ≫ (e A).hom =
          (e B).hom ≫ restrictedOverCohomologyMap k
            ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)
            (q : ℤ) f U := by
  obtain ⟨e, he⟩ := exists_rawModule_abelianHom_comparison Λ k G q U
  obtain ⟨r, hr⟩ := exists_raw_restricted_cohomology_natural_iso S q U
  let F := (sheafCompose _
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G
  refine ⟨fun A ↦ e A ≪≫ r (A.hom ≫ k) (restrictedOverCoefficient F A), ?_⟩
  intro A B f
  apply AddCommGrpCat.ext
  intro z
  change (r (A.hom ≫ k) (restrictedOverCoefficient F A)).hom
      ((e A).hom ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z)) =
    restrictedOverCohomologyMap k F (q : ℤ) f U
      ((r (B.hom ≫ k) (restrictedOverCoefficient F B)).hom ((e B).hom z))
  rw [he]
  exact (hr f.left (B.hom ≫ k) (A.hom ≫ k)
    (by rw [← Category.assoc, Over.w])
    (restrictedOverCoefficient F B) (restrictedOverCoefficient F A)
    ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
      (Over.w f).symm).inv.app F) ((e B).hom z)).symm
end AlgebraicGeometry.Etale
