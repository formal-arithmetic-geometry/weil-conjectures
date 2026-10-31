/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.OpenScalarTensorData
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTowerSupplement
public import WeilConjectures.SecSmoothPurity.ScalarExtensionFunctor
public import WeilConjectures.Algebra.Homology.ScalarInternalHomDataSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale SheafOfModules
open AlgebraicGeometry.ProEtale.OpenScalarTensor
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor
/-- The right-adjoint comparison left after the presentation normalization.
Source: Stacks 03DA, 07A6 and 0D6D.
(blueprint: lem-sp-open-scalar-coefficient-conjugate-comparison).

Proof: replace the composite ring map ψ.comp φ by an arbitrary c with a ≫ b = c and
substitute c := a ≫ b. The transport between the two scalar pairs is then the identity, whose
conjugate is the identity. The ordinary restriction comparison for a ≫ b is the identity on
sections, so by its uniqueness (03DA) it is the identity isomorphism; the ordinary comparison
inside scalarHomRestrictionComp is the identity by definition. Both sides are therefore the
inverse of the derived composition isomorphism followed by the derived image of an identity. -/
theorem scalarRestrictionConjugateComparison
    (m : Models.{u}) {T : Scheme.{u}} [EssentiallySmall.{u + 1} T.ProEt]
    [(ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) :
    (CategoryTheory.scalarHomRestrictionComp.{u + 1, u, u + 1}
      (proEtaleConstantRingMap (T := T) φ)
      (proEtaleConstantRingMap (T := T) ψ)).inv ≫
      conjugateEquiv ((m T).scalar
        (proEtaleConstantRingMap (T := T) φ ≫ proEtaleConstantRingMap (T := T) ψ)).adjunction
        (scalarPair m (ψ.comp φ) T).adjunction
        (eqToHom (congrArg (fun q => ((m T).scalar q).derived)
          (scalarExtensionFunctor_ringMap_comp φ ψ T).symm)) =
      (pbcDerivedRestrictComp (proEtaleConstantRingMap (T := T) φ)
        (proEtaleConstantRingMap (T := T) ψ)
        (proEtaleConstantRingMap (T := T) (ψ.comp φ))
        (scalarExtensionFunctor_ringMap_comp φ ψ T)).hom := by
  have hres : ∀ {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) (b : S ⟶ V),
      pbcRestrictComp a b (a ≫ b) rfl = Iso.refl _ := by
    intro R S V a b
    apply (pbcRestrictComp_exists a b (a ≫ b) rfl).unique
    · exact (pbcRestrictComp_exists a b (a ≫ b) rfl).exists.choose_spec
    · intro M U x
      rfl
  have key : ∀ (c : proEtaleConstantRing T A ⟶ proEtaleConstantRing T C)
      (h : proEtaleConstantRingMap (T := T) φ ≫ proEtaleConstantRingMap (T := T) ψ = c),
      (CategoryTheory.scalarHomRestrictionComp.{u + 1, u, u + 1}
        (proEtaleConstantRingMap (T := T) φ)
        (proEtaleConstantRingMap (T := T) ψ)).inv ≫
        conjugateEquiv ((m T).scalar
          (proEtaleConstantRingMap (T := T) φ ≫ proEtaleConstantRingMap (T := T) ψ)).adjunction
          ((m T).scalar c).adjunction
          (eqToHom (congrArg (fun q => ((m T).scalar q).derived) h.symm)) =
        (pbcDerivedRestrictComp (proEtaleConstantRingMap (T := T) φ)
          (proEtaleConstantRingMap (T := T) ψ) c h).hom := by
    intro c h
    subst h
    rw [eqToHom_refl, conjugateEquiv_id, Category.comp_id]
    unfold pbcDerivedRestrictComp CategoryTheory.scalarHomRestrictionComp
    rw [hres]
    simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom]
    rw [← Functor.mapDerivedCategoryNatIso_symm]
    rfl
  exact key _ _

end AlgebraicGeometry.ProEtale.OpenScalarTensor
