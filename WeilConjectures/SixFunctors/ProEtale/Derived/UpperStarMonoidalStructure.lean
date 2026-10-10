/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.Monoidal.MapOplaxMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLocalization
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidal

/-!
# The derived pullback is a monoidal functor

Let `g : Z ⟶ Y` be a morphism of schemes such that `g^*` preserves flat pro-étale sheaves.
We show that the derived pullback `Lg^* : D(Y_proét) ⥤ D(Z_proét)` is a monoidal functor
for the derived tensor products, its comonoidal structure being the comparison
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison`.

The coherence axioms are deduced, with `CategoryTheory.Functor.Monoidal.ofLocalization`, from
those of the monoidal functor `g^* : K(Y_proét) ⥤ K(Z_proét)` induced on homotopy categories,
by checking the compatibility of the structure maps on the complexes `K` which are K-flat and
whose pullback `g^*K` is K-flat. These are stable under tensor products, contain the unit, and
every object of `D(Y_proét)` is isomorphic to the image of such a complex (a functorial flat
resolution).

## Main definitions

- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarLocalizationData A g`: the data
  `CategoryTheory.Functor.OplaxMonoidal.LocalizationData` for the square
  `Qh ⋙ Lg^* ≅ g^* ⋙ Qh`.
- `AlgebraicGeometry.ProEtale.monoidalLeftDerivedUpperStar A g`: the monoidal structure on
  `Lg^*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {A} in
/-- The unit `𝟙 ⟶ Qh 𝟙` of the lax monoidal functor `Qh : K(X_proét) ⥤ D(X_proét)` is an
isomorphism. -/
instance isIso_ε_Qh {X : Scheme.{u}} :
    IsIso (ε (Qh (C := Sheaf (Scheme.ProEt.topology X) A))) :=
  inferInstanceAs (IsIso (ε (toDerivedMonoidal Qh
    (HomotopyCategory.quasiIso (Sheaf (Scheme.ProEt.topology X) A) (.up ℤ)))))

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

omit [Abelian.HasFunctorialFlatResolution A] in
/-- The complexes `K` whose pullback `g^*K` is K-flat are stable under tensor products. -/
lemma kFlatUpperStar_tensor
    {K M : HomotopyCategory (Sheaf (Scheme.ProEt.topology Y) A) (.up ℤ)}
    (hK : kFlatUpperStar A g K) (hM : kFlatUpperStar A g M) :
    kFlatUpperStar A g (K ⊗ M) :=
  (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat.prop_of_iso
    (Functor.Monoidal.μIso ((g)^*[A].mapHomotopyCategory (.up ℤ)) K M)
    (ObjectProperty.prop_tensor hK hM)

omit [Abelian.HasFunctorialFlatResolution A] in
/-- The unit complex lies in `kFlatUpperStar A g`. -/
lemma kFlatUpperStar_unit :
    kFlatUpperStar A g (𝟙_ (HomotopyCategory (Sheaf (Scheme.ProEt.topology Y) A) (.up ℤ))) :=
  (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat.prop_of_iso
    (Functor.Monoidal.εIso ((g)^*[A].mapHomotopyCategory (.up ℤ)))
    (ObjectProperty.prop_unit _)

/-- Every object of `D(Y_proét)` is isomorphic to the image of a K-flat complex whose pullback
by `g` is K-flat, namely a functorial flat resolution. -/
lemma exists_kFlat_kFlatUpperStar_iso [(g)^*[A].PreservesFlat]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ∃ X, ((HomotopyCategory.quasiIso _ (.up ℤ)).kFlat ⊓ kFlatUpperStar A g) X ∧
      Nonempty (Qh.obj X ≅ K) := by
  let Λ := (inferInstance :
    HasFunctorialFlatResolution (Sheaf (Scheme.ProEt.topology Y) A)).some.reduced
  obtain ⟨K₀, hK₀⟩ := (Qh.objPreimage K).quotient_obj_surjective
  refine ⟨(HomotopyCategory.quotient _ _).obj (Λ.resolutionFunctor.obj K₀),
    ⟨(HomotopyCategory.kFlat_quotient_obj_iff _).2
      (Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K₀),
      kFlatUpperStar_quotient_obj_resolutionFunctor_obj A g Λ K₀⟩,
    ⟨Localization.isoOfHom Qh (HomotopyCategory.quasiIso _ (.up ℤ))
      ((HomotopyCategory.quotient _ _).map (Λ.resolutionNatTrans.app K₀)) ?_ ≪≫
        Qh.mapIso (eqToIso hK₀) ≪≫ Qh.objObjPreimageIso K⟩⟩
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
  infer_instance

/-- The compatibility of the comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M` with the
comonoidal structure of `g^* : K(Y_proét) ⥤ K(Z_proét)`, through the counit of `Lg^*` and the lax
monoidal structures of `Qh`. -/
lemma leftDerivedUpperStarTensorComparison_fac [(g)^*[A].PreservesFlat]
    (K M : HomotopyCategory (Sheaf (Scheme.ProEt.topology Y) A) (.up ℤ)) :
    ((leftDerivedUpperStarTensorComparison A g).app (Qh.obj K)).app (Qh.obj M) ≫
        ((g)^*[A].leftDerivedFunctorCounit.app K ⊗ₘ (g)^*[A].leftDerivedFunctorCounit.app M) ≫
        μ Qh (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj K)
          (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj M) =
      L((g)^*[A]).map (μ Qh K M) ≫ (g)^*[A].leftDerivedFunctorCounit.app (K ⊗ M) ≫
        Qh.map (δ ((g)^*[A].mapHomotopyCategory (.up ℤ)) K M) := by
  rw [tensorHom_def, Category.assoc]
  have := isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar A g
  have h := Functor.leftDerived₂NatTrans_app_app (derivedTensorLeftDerivedUpperStar A g)
    (derivedTensorLeftDerivedUpperStarCounit A g) (HomotopyCategory.quasiIso _ (.up ℤ))
    (HomotopyCategory.quasiIso _ (.up ℤ)) _ (leftDerivedUpperStarDerivedTensorCounit A g)
    (Functor.postcompose₂MapWhiskeringLeft₂ (mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh)
    K M
  simp only [derivedTensorLeftDerivedUpperStarCounit, leftDerivedUpperStarDerivedTensorCounit,
    NatTrans.comp_app, Category.assoc] at h
  exact h

/-- The data `CategoryTheory.Functor.OplaxMonoidal.LocalizationData` for the square
`Qh ⋙ Lg^* ≅ g^* ⋙ Qh` given by the counit of `Lg^*`: the comonoidal structure is the
comparison `leftDerivedUpperStarTensorComparison`, and the good complexes are the K-flat
complexes whose pullback by `g` is K-flat. -/
noncomputable def leftDerivedUpperStarLocalizationData [(g)^*[A].PreservesFlat] :
    Functor.OplaxMonoidal.LocalizationData Qh Qh ((g)^*[A].mapHomotopyCategory (.up ℤ))
      L((g)^*[A]) (asIso (g)^*[A].leftDerivedFunctorCounit) where
  P := (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat ⊓ kFlatUpperStar A g
  δ K M := ((leftDerivedUpperStarTensorComparison A g).app K).app M
  δ_natural_left f M :=
    NatTrans.congr_app ((leftDerivedUpperStarTensorComparison A g).naturality f) M
  δ_natural_right K _ _ f := ((leftDerivedUpperStarTensorComparison A g).app K).naturality f
  η := L((g)^*[A]).map (ε Qh) ≫ (g)^*[A].leftDerivedFunctorCounit.app _ ≫
    Qh.map (η ((g)^*[A].mapHomotopyCategory (.up ℤ))) ≫ inv (ε Qh)
  tensor_mem hK hM :=
    ⟨ObjectProperty.prop_tensor hK.1 hM.1, kFlatUpperStar_tensor A g hK.2 hM.2⟩
  unit_mem := ⟨ObjectProperty.prop_unit _, kFlatUpperStar_unit A g⟩
  essSurj := exists_kFlat_kFlatUpperStar_iso A g
  isIso_μ' _ hM := isIso_μNatTrans_Qh_app_app_of_kFlat _ _ hM.2
  isIso_δ _ _ := inferInstance
  fac {K M} _ _ := leftDerivedUpperStarTensorComparison_fac A g K M
  fac_η := by simp

/-- The comonoidal structure of `leftDerivedUpperStarLocalizationData` is an isomorphism. -/
instance isIso_leftDerivedUpperStarLocalizationData_δ [(g)^*[A].PreservesFlat]
    (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    IsIso ((leftDerivedUpperStarLocalizationData A g).δ K M) :=
  inferInstanceAs (IsIso (((leftDerivedUpperStarTensorComparison A g).app K).app M))

/-- The counit of `leftDerivedUpperStarLocalizationData` is an isomorphism. -/
instance isIso_leftDerivedUpperStarLocalizationData_η [(g)^*[A].PreservesFlat] :
    IsIso (leftDerivedUpperStarLocalizationData A g).η := by
  dsimp only [leftDerivedUpperStarLocalizationData]
  infer_instance

/-- The derived pullback `Lg^* : D(Y_proét) ⥤ D(Z_proét)` is a monoidal functor, with
comonoidal structure the comparison `leftDerivedUpperStarTensorComparison`
(`AlgebraicGeometry.ProEtale.monoidalLeftDerivedUpperStar_δ`). -/
@[instance_reducible]
noncomputable def monoidalLeftDerivedUpperStar [(g)^*[A].PreservesFlat] :
    (L((g)^*[A])).Monoidal :=
  Functor.Monoidal.ofLocalization (leftDerivedUpperStarLocalizationData A g)

@[simp]
lemma monoidalLeftDerivedUpperStar_δ [(g)^*[A].PreservesFlat]
    (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    letI := monoidalLeftDerivedUpperStar A g
    δ L((g)^*[A]) K M = ((leftDerivedUpperStarTensorComparison A g).app K).app M :=
  rfl

@[simp]
lemma monoidalLeftDerivedUpperStar_μIso [(g)^*[A].PreservesFlat]
    (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    letI := monoidalLeftDerivedUpperStar A g
    Functor.Monoidal.μIso L((g)^*[A]) K M = (leftDerivedUpperStarTensorIso A g K M).symm := by
  rw [← Iso.symm_eq_iff, Iso.symm_symm_eq]
  exact Iso.ext rfl

@[simp]
lemma monoidalLeftDerivedUpperStar_η [(g)^*[A].PreservesFlat] :
    letI := monoidalLeftDerivedUpperStar A g
    η L((g)^*[A]) = L((g)^*[A]).map (ε Qh) ≫ (g)^*[A].leftDerivedFunctorCounit.app _ ≫
      Qh.map (η ((g)^*[A].mapHomotopyCategory (.up ℤ))) ≫ inv (ε Qh) :=
  rfl

end ProEtale

end AlgebraicGeometry
