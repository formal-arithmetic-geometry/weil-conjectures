/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidal

/-!
# The derived pullback of pro-étale sheaves is a monoidal functor

This is the pro-étale counterpart of the section `Monoidal` of
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`.

For `g : Z ⟶ Y`, the tensor comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M`
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison`) is the comonoidal structure
of an oplax monoidal structure on `Lg^* : D(Y_proét) ⥤ D(Z_proét)`, whose structure maps are
isomorphisms. The coherence axioms are checked on complexes whose pullback is K-flat
(`CategoryTheory.Functor.OplaxMonoidal.ofLaxSquare`).

## Main definitions and results

- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarOplaxMonoidal g`: the oplax monoidal structure
  on `Lg^*`, with comonoidal structure `leftDerivedUpperStarTensorComparison`.
- `AlgebraicGeometry.ProEtale.isIso_leftDerivedUpperStarOplaxMonoidal_δ` and
  `AlgebraicGeometry.ProEtale.isIso_leftDerivedUpperStarOplaxMonoidal_η`: its structure maps are
  isomorphisms.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarMonoidal g`: `Lg^*` as a monoidal functor.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

section Monoidal

open DerivedCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable [ProEtale.UpperStarPreservesFlat A]

attribute [local instance] isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor

/-- The tensor comparison `Lg^*(Qh K ⊗ᴸ Qh M) ⟶ Lg^*(Qh K) ⊗ᴸ Lg^*(Qh M)` is induced by the
comonoidal structure of `g^*` on homotopy categories, through the counits of `Lg^*`. -/
lemma leftDerivedUpperStarTensorComparison_app_app_comp
    (K M : HomotopyCategory (Sheaf (Scheme.ProEt.topology Y) A) (.up ℤ)) :
    ((leftDerivedUpperStarTensorComparison A g).app (Qh.obj K)).app (Qh.obj M) ≫
        ((g)^*[A].leftDerivedFunctorCounit.app K ⊗ₘ (g)^*[A].leftDerivedFunctorCounit.app M) ≫
          μ Qh (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj K)
            (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj M) =
      L((g)^*[A]).map (μ Qh K M) ≫ (g)^*[A].leftDerivedFunctorCounit.app (K ⊗ M) ≫
        Qh.map (δ ((g)^*[A].mapHomotopyCategory (.up ℤ)) K M) := by
  have h := Functor.leftDerived₂NatTrans_app_app _ (derivedTensorLeftDerivedUpperStarCounit A g)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedUpperStarDerivedTensorCounit A g)
    (Functor.postcompose₂MapWhiskeringLeft₂ (mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh)
    K M
  have e₁ : ((derivedTensorLeftDerivedUpperStarCounit A g).app K).app M =
      ((g)^*[A].leftDerivedFunctorCounit.app K ⊗ₘ (g)^*[A].leftDerivedFunctorCounit.app M) ≫
        μ Qh (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj K)
          (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj M) := by
    rw [tensorHom_def]
    dsimp [derivedTensorLeftDerivedUpperStarCounit, derivedTensor]
    rw [Category.assoc]
    rfl
  have e₂ : ((leftDerivedUpperStarDerivedTensorCounit A g).app K).app M =
      L((g)^*[A]).map (μ Qh K M) ≫ (g)^*[A].leftDerivedFunctorCounit.app (K ⊗ M) := rfl
  have e₃ : ((Functor.postcompose₂MapWhiskeringLeft₂
      (mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh).app K).app M =
      Qh.map (δ ((g)^*[A].mapHomotopyCategory (.up ℤ)) K M) := rfl
  rw [e₁, e₂, e₃] at h
  simp only [Category.assoc] at h
  exact h

/-- Every complex in `D(Y_proét)` is isomorphic to `Qh P` for a complex `P` whose pullback by `g`
is K-flat. -/
lemma exists_kFlatUpperStar_iso (X : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ∃ P, kFlatUpperStar A g P ∧ Nonempty (Qh.obj P ≅ X) := by
  have := Localization.essSurj (Qh (C := Sheaf (Scheme.ProEt.topology Y) A))
    (HomotopyCategory.quasiIso _ (.up ℤ))
  obtain ⟨R⟩ := LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftResolutions
    (Φ := HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)) (Qh.objPreimage X)
  have hR : IsIso (Qh.map R.w) := Localization.inverts Qh (HomotopyCategory.quasiIso _ _) _ R.hw
  exact ⟨R.X₁.obj, R.X₁.property, ⟨@asIso _ _ _ _ (Qh.map R.w) hR ≪≫ Qh.objObjPreimageIso X⟩⟩

/-- The oplax monoidal structure on the derived pullback `Lg^* : D(Y_proét) ⥤ D(Z_proét)`, whose
comonoidal structure is the tensor comparison `leftDerivedUpperStarTensorComparison`. It is
induced by the oplax monoidal structure of `g^*` on homotopy categories
(`Functor.mapHomotopyCategoryOplaxMonoidal`), computing on complexes whose pullback is K-flat. -/
@[instance_reducible]
noncomputable def leftDerivedUpperStarOplaxMonoidal : L((g)^*[A]).OplaxMonoidal :=
  haveI := DerivedCategory.isIso_ε_Qh (Sheaf (Scheme.ProEt.topology Z) A)
  Functor.OplaxMonoidal.ofLaxSquare (Q₁ := Qh) (Q₂ := Qh)
    (F := (g)^*[A].mapHomotopyCategory (.up ℤ)) (leftDerivedUpperStarTensorComparison A g)
    (fun a ↦ (g)^*[A].leftDerivedFunctorCounit.app a)
    (fun _ _ f ↦ (g)^*[A].leftDerivedFunctorCounit.naturality f)
    (leftDerivedUpperStarTensorComparison_app_app_comp A g) (kFlatUpperStar A g)
    (exists_kFlatUpperStar_iso A g) (fun x _ hb ↦ isIso_μNatTrans_Qh_app_app_of_kFlat x _ hb)

lemma isIso_leftDerivedUpperStarOplaxMonoidal_δ
    (X X' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    letI := leftDerivedUpperStarOplaxMonoidal A g
    IsIso (δ L((g)^*[A]) X X') :=
  inferInstanceAs (IsIso (((leftDerivedUpperStarTensorComparison A g).app X).app X'))

lemma isIso_leftDerivedUpperStarOplaxMonoidal_η :
    letI := leftDerivedUpperStarOplaxMonoidal A g
    IsIso (η L((g)^*[A])) := by
  have := DerivedCategory.isIso_ε_Qh (Sheaf (Scheme.ProEt.topology Z) A)
  have := DerivedCategory.isIso_ε_Qh (Sheaf (Scheme.ProEt.topology Y) A)
  have : IsIso (η ((g)^*[A].mapHomotopyCategory (.up ℤ))) := by
    rw [Functor.mapHomotopyCategory_η]
    exact (HomotopyCategory.quotient _ _).map_isIso
      (η ((g)^*[A].mapHomologicalComplex (.up ℤ)))
  exact inferInstanceAs (IsIso (L((g)^*[A]).map (ε Qh) ≫
    (g)^*[A].leftDerivedFunctorCounit.app (𝟙_ _) ≫
      Qh.map (η ((g)^*[A].mapHomotopyCategory (.up ℤ))) ≫ CategoryTheory.inv (ε Qh)))

/-- The derived pullback `Lg^* : D(Y_proét) ⥤ D(Z_proét)` as a monoidal functor: the oplax monoidal
structure `leftDerivedUpperStarOplaxMonoidal`, whose structure maps are isomorphisms. -/
@[instance_reducible]
noncomputable def leftDerivedUpperStarMonoidal : L((g)^*[A]).Monoidal :=
  letI := leftDerivedUpperStarOplaxMonoidal A g
  haveI := isIso_leftDerivedUpperStarOplaxMonoidal_δ A g
  haveI := isIso_leftDerivedUpperStarOplaxMonoidal_η A g
  (Functor.CoreMonoidal.ofOplaxMonoidal _).toMonoidal

end Monoidal

end ProEtale

end AlgebraicGeometry
