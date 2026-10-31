/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MateCounit
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalOfIso
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReduction
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionMonoidalSheaf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullFacGeneric

/-!
# The commutation of the reduction of coefficients with the derived pullback is monoidal

Let `ρ : Λ →+* Λ'` be a surjective morphism of commutative rings with principal kernel and `Ψ`
the derived extension of scalars (`AlgebraicGeometry.Etale.derivedExtendScalars`). For a morphism
of schemes `e : U ⟶ X`, the commutation `Le^* ⋙ Ψ_U ≅ Ψ_X ⋙ Le^*`
(`AlgebraicGeometry.Etale.derivedExtendScalarsPullbackIso`), defined as a mate, is, through the
counits of the left derived functors, the underived commutation of the extension of scalars of
étale sheaves with the pullback (`AlgebraicGeometry.Etale.extendScalarsUpperStarIso`)
(`AlgebraicGeometry.Etale.derivedExtendScalarsPullbackMap_eq`). As the latter is monoidal, so is
the former: it is compatible with the tensor comparisons of `Ψ` and of the derived pullbacks
(`AlgebraicGeometry.Etale.derivedExtendScalarsPullbackMap_app_tensor_comp_δ`) and with the unit
comparisons (`AlgebraicGeometry.Etale.derivedExtendScalarsPullbackMap_app_unit_comp_η`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

-- the instances used in the definitions of the derived tensor products, as in
-- `WeilConjectures.SixFunctors.Etale.Derived.ReductionHom`
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- Preserving quasi-isomorphisms between K-flat complexes is invariant under isomorphism of
functors. -/
lemma preservesKFlatQuasiIso_of_iso {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G)
    [F.PreservesKFlatQuasiIso] : G.PreservesKFlatQuasiIso where
  quasiIso_map hK hL f _ := by
    have := F.quasiIso_mapHomologicalComplex_map_of_kFlat hK hL f
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoOfNatIso (NatIso.mapHomologicalComplex e (.up ℤ)) (Arrow.mk f))).1 this

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})

section Counit

variable (X : Scheme.{u})

/-- The counit of the derived adjunction `Ψ ⊣ Res` on the image of a complex `M` is the levelwise
counit, read through the counit of `Ψ`. -/
lemma derivedExtendScalarsAdjunction_counit_app_Qh
    (M : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) (.up ℤ)) :
    (derivedExtendScalarsAdjunction hρ ha X).counit.app (DerivedCategory.Qh.obj M) =
      (derivedExtendScalars hρ ha X).map
          ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.app M) ≫
        (derivedExtendScalarsCounit hρ ha X).app
          (((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).obj M) ≫
        DerivedCategory.Qh.map (((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).mapHomotopyCategory
          (.up ℤ)).counit.app M) := by
  have := preservesKFlatQuasiIso_extendScalars hρ ha X
  have h₁ := (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)
    |>.derivedε_fac_app (HomotopyCategory.quasiIso _ (.up ℤ))
      (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorCounit
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).rightDerivedFunctorUnit M
  have h₃ := NatTrans.congr_app
    (Sheaf.restrictScalars X.smallEtaleTopology ρ).rightDerivedFunctorIsoMapDerivedCategory_hom_fac M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₃
  delta derivedExtendScalarsAdjunction derivedExtendScalars derivedExtendScalarsCounit
  dsimp only
  simp only [Adjunction.derivedAdjunction, Adjunction.ofNatIsoRight_counit, NatTrans.comp_app]
  rw [Functor.whiskerRight_app, Adjunction.derived_counit]
  have hu : (Sheaf.restrictScalars X.smallEtaleTopology ρ).rightDerivedFunctorUnit.app M =
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.inv.app M ≫
        (Sheaf.restrictScalars X.smallEtaleTopology ρ).rightDerivedFunctorIsoMapDerivedCategory.inv.app
          (DerivedCategory.Qh.obj M) := by
    rw [← h₃, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  rw [hu, Functor.map_comp, Category.assoc] at h₁
  rw [← h₁, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

end Counit

section PullbackCounit

variable {U X : Scheme.{u}} (e : U ⟶ X)

/-- The counit `Qh ⋙ Ψ_X ⋙ Le^* ⟶ F_X ⋙ e^* ⋙ Qh` of the composite of the derived extension of
scalars with the derived pullback. -/
noncomputable abbrev derivedExtendScalarsUpperStarCounit :
    DerivedCategory.Qh ⋙ derivedExtendScalars hρ ha X ⋙ L((e)^*[ModuleCat.{u + 1} Λ']) ⟶
      (Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ) ⋙
        ((e)^*[ModuleCat.{u + 1} Λ']).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.whiskerRight (derivedExtendScalarsCounit hρ ha X) L((e)^*[ModuleCat.{u + 1} Λ']) ≫
    Functor.whiskerLeft ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ))
      ((e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctorCounit

/-- The counit `Qh ⋙ Le^* ⋙ Ψ_U ⟶ e^* ⋙ F_U ⋙ Qh` of the composite of the derived pullback with
the derived extension of scalars. -/
noncomputable abbrev upperStarDerivedExtendScalarsCounit :
    DerivedCategory.Qh ⋙ L((e)^*[ModuleCat.{u + 1} Λ]) ⋙ derivedExtendScalars hρ ha U ⟶
      ((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ) ⋙
        (Sheaf.extendScalars U.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh :=
  Functor.whiskerRight ((e)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctorCounit
      (derivedExtendScalars hρ ha U) ≫
    Functor.whiskerLeft (((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ))
      (derivedExtendScalarsCounit hρ ha U)

/-- `Ψ_X ⋙ Le^*` is a left derived functor of `F_X ⋙ e^*`: on a K-flat complex, both counits
are isomorphisms. -/
instance isLeftDerivedFunctor_derivedExtendScalarsUpperStarCounit :
    (derivedExtendScalars hρ ha X ⋙ L((e)^*[ModuleCat.{u + 1} Λ'])).IsLeftDerivedFunctor
      (derivedExtendScalarsUpperStarCounit hρ ha e) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat _ ?_
  rintro ⟨K, hK⟩
  have := preservesKFlatQuasiIso_extendScalars hρ ha X
  have h₁ : IsIso ((derivedExtendScalarsCounit hρ ha X).app
      ((HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat.functor.obj ⟨K, hK⟩)) :=
    (Sheaf.extendScalars X.smallEtaleTopology ρ).isIso_leftDerivedFunctorCounit_app_of_kFlat' K hK
  have h₂ : IsIso (((e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctorCounit.app
      (((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).obj K)) :=
    inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _) h₂

/-- `Le^* ⋙ Ψ_U` is a left derived functor of `e^* ⋙ F_U`: on a complex whose pullback is
K-flat, both counits are isomorphisms. -/
instance isLeftDerivedFunctor_upperStarDerivedExtendScalarsCounit :
    (L((e)^*[ModuleCat.{u + 1} Λ]) ⋙ derivedExtendScalars hρ ha U).IsLeftDerivedFunctor
      (upperStarDerivedExtendScalarsCounit hρ ha e) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIsoLocalizerMorphism ((e)^*[ModuleCat.{u + 1} Λ]).kFlatMap) _ ?_
  rintro ⟨K, hK⟩
  have := preservesKFlatQuasiIso_extendScalars hρ ha U
  have h₁ : IsIso (((e)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctorCounit.app K) := inferInstance
  have h₂ : IsIso ((derivedExtendScalarsCounit hρ ha U).app
      ((((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ)).obj K)) :=
    (Sheaf.extendScalars U.smallEtaleTopology ρ).isIso_leftDerivedFunctorCounit_app_of_kFlat' _ hK
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _) h₂

variable (ρ) in
/-- The isomorphism `F_X ⋙ e^* ≅ e^* ⋙ F_U` on homotopy categories. -/
noncomputable def extendScalarsUpperStarHomotopyIso :
    (Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ) ⋙
        ((e)^*[ModuleCat.{u + 1} Λ']).mapHomotopyCategory (.up ℤ) ≅
      ((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ) ⋙
        (Sheaf.extendScalars U.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ) ≪≫
    { hom := NatTrans.mapHomotopyCategory (extendScalarsUpperStarIso ρ e).hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory (extendScalarsUpperStarIso ρ e).inv (.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id, NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id, NatTrans.mapHomotopyCategory_id] } ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).symm

/-- The commutation `Le^* ⋙ Ψ_U ≅ Ψ_X ⋙ Le^*` of left derived functors induced by the
underived commutation `F_X ⋙ e^* ≅ e^* ⋙ F_U`. -/
noncomputable def derivedExtendScalarsPullbackIsoOfCounit :
    L((e)^*[ModuleCat.{u + 1} Λ]) ⋙ derivedExtendScalars hρ ha U ≅
      derivedExtendScalars hρ ha X ⋙ L((e)^*[ModuleCat.{u + 1} Λ']) :=
  Functor.leftDerivedNatIso _ _ (upperStarDerivedExtendScalarsCounit hρ ha e)
    (derivedExtendScalarsUpperStarCounit hρ ha e) (HomotopyCategory.quasiIso _ (.up ℤ))
    (Functor.isoWhiskerRight (extendScalarsUpperStarHomotopyIso ρ e).symm DerivedCategory.Qh)

/-- The commutation `Le^* ⋙ Ψ_U ≅ Ψ_X ⋙ Le^*` of left derived functors is induced, through the
counits, by the underived commutation. -/
@[reassoc]
lemma derivedExtendScalarsPullbackIsoOfCounit_hom_app_Qh
    (K : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ)) :
    (derivedExtendScalarsPullbackIsoOfCounit hρ ha e).hom.app (DerivedCategory.Qh.obj K) ≫
        (derivedExtendScalarsUpperStarCounit hρ ha e).app K =
      (upperStarDerivedExtendScalarsCounit hρ ha e).app K ≫
        DerivedCategory.Qh.map ((extendScalarsUpperStarHomotopyIso ρ e).inv.app K) :=
  Functor.leftDerivedNatTrans_app _ _ _ _ (HomotopyCategory.quasiIso _ (.up ℤ)) _ K

/-- **The commutation of `Ψ` with the derived pullbacks through the counits**: the mate
`derivedExtendScalarsPullbackMap` of `Res ⋙ Le^* ≅ Le^* ⋙ Res` is the commutation of left
derived functors induced by the underived commutation `F_X ⋙ e^* ≅ e^* ⋙ F_U`. -/
theorem derivedExtendScalarsPullbackMap_eq :
    derivedExtendScalarsPullbackMap hρ ha e = (derivedExtendScalarsPullbackIsoOfCounit hρ ha e).hom := by
  have h := Adjunction.mateEquiv_leftDerived_inv_eq
    (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ)
    (Sheaf.extendScalarsAdjunction U.smallEtaleTopology ρ)
    (extendScalarsUpperStarIso ρ e) (upperStarRestrictScalarsIso ρ e)
    (mateEquiv_extendScalarsUpperStarIso_inv ρ e) (extendScalarsUpperStarHomotopyIso ρ e)
    (by simp [extendScalarsUpperStarHomotopyIso])
    (derivedExtendScalarsCounit hρ ha X) (derivedExtendScalarsCounit hρ ha U)
    ((e)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctorCounit
    (leftDerivedUpperStarIsoMapDerivedCategory _ e)
    ((e)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac
    ((e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctorCounit
    (leftDerivedUpperStarIsoMapDerivedCategory _ e)
    ((e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac
    (derivedExtendScalarsAdjunction hρ ha X) (derivedExtendScalarsAdjunction hρ ha U)
    (derivedExtendScalarsAdjunction_counit_app_Qh hρ ha X)
    (derivedExtendScalarsAdjunction_counit_app_Qh hρ ha U)
    (derivedExtendScalarsPullbackIsoOfCounit hρ ha e).symm _ rfl _ rfl
    (derivedExtendScalarsPullbackIsoOfCounit_hom_app_Qh hρ ha e)
    (leftDerivedUpperStarRestrictScalarsIso ρ e) rfl
  rw [Iso.symm_inv] at h
  rw [derivedExtendScalarsPullbackMap, ← h, Equiv.symm_apply_apply]

end PullbackCounit

/-- The comonoidal structure of `Ψ` is the tensor comparison of the left derived functor. -/
lemma derivedExtendScalarsMonoidal_δ (X : Scheme.{u})
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    letI := derivedExtendScalarsMonoidal hρ ha X
    haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
    Functor.OplaxMonoidal.δ (derivedExtendScalars hρ ha X) K M =
      (((Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedTensorComparison.app K).app M) :=
  rfl

section Tensor

variable {U X : Scheme.{u}} (e : U ⟶ X)

open Functor.OplaxMonoidal in
/-- **The commutation of `Ψ` with the derived pullback is compatible with the tensor
comparisons**: for `K, M ∈ D(X_ét, Λ)`, the square
```
Ψ_U Le^*(K ⊗ᴸ M) ──≅──▶ Le^* Ψ_X (K ⊗ᴸ M) ──≅──▶ Le^*(Ψ_X K ⊗ᴸ Ψ_X M) ──≅──▶ Le^*Ψ_X K ⊗ᴸ Le^*Ψ_X M
       │ ≅                                                                        ▲ ≅
       ▼                                                                          │
Ψ_U(Le^* K ⊗ᴸ Le^* M) ──────────≅─────────▶ Ψ_U Le^* K ⊗ᴸ Ψ_U Le^* M ─────────────┘
```
commutes. Through the counits, the commutation is the underived commutation
`F_X ⋙ e^* ≅ e^* ⋙ F_U` (`AlgebraicGeometry.Etale.derivedExtendScalarsPullbackMap_eq`), which is
monoidal (`AlgebraicGeometry.Etale.isMonoidal_extendScalarsUpperStarIso_hom`). -/
theorem derivedExtendScalarsPullbackMap_app_tensor_comp_δ
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    letI := derivedExtendScalarsMonoidal hρ ha X
    letI := derivedExtendScalarsMonoidal hρ ha U
    (derivedExtendScalarsPullbackMap hρ ha e).app (K ⊗ M) ≫
        L((e)^*[ModuleCat.{u + 1} Λ']).map (δ (derivedExtendScalars hρ ha X) K M) ≫
          ((leftDerivedUpperStarTensorComparison _ e).app _).app _ =
      (derivedExtendScalars hρ ha U).map
          (((leftDerivedUpperStarTensorComparison _ e).app K).app M) ≫
        δ (derivedExtendScalars hρ ha U) _ _ ≫
          ((derivedExtendScalarsPullbackMap hρ ha e).app K ⊗ₘ
            (derivedExtendScalarsPullbackMap hρ ha e).app M) := by
  let := derivedExtendScalarsMonoidal hρ ha X
  let := derivedExtendScalarsMonoidal hρ ha U
  have := preservesKFlatQuasiIso_extendScalars hρ ha X
  have := preservesKFlatQuasiIso_extendScalars hρ ha U
  have := isMonoidal_extendScalarsUpperStarIso_hom ρ e
  have : ((e)^*[ModuleCat.{u + 1} Λ] ⋙ Sheaf.extendScalars U.smallEtaleTopology ρ).PreservesKFlatQuasiIso :=
    Functor.preservesKFlatQuasiIso_of_iso (extendScalarsUpperStarIso ρ e)
  -- the comparison `Le^* ⋙ Ψ_U ≅ L(e^* ⋙ F_U)`, through the counits
  let γ := Functor.leftDerivedNatIso (L((e)^*[ModuleCat.{u + 1} Λ]) ⋙ derivedExtendScalars hρ ha U)
    ((e)^*[ModuleCat.{u + 1} Λ] ⋙ Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctor
    (upperStarDerivedExtendScalarsCounit hρ ha e)
    ((e)^*[ModuleCat.{u + 1} Λ] ⋙ Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctorCounit
    (HomotopyCategory.quasiIso _ (.up ℤ))
    (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl ((e)^*[ModuleCat.{u + 1} Λ] ⋙ Sheaf.extendScalars U.smallEtaleTopology ρ)) (.up ℤ))
      DerivedCategory.Qh)
  have hγ (P : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ)) :
      γ.hom.app (DerivedCategory.Qh.obj P) ≫
        ((e)^*[ModuleCat.{u + 1} Λ] ⋙
          Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctorCounit.app P =
      (Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctor.map
          (((e)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctorCounit.app P) ≫
        (Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctorCounit.app
          ((((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl ((e)^*[ModuleCat.{u + 1} Λ] ⋙ Sheaf.extendScalars U.smallEtaleTopology ρ))
            (.up ℤ)).hom.app P) := by
    have h := Functor.leftDerivedNatTrans_app _ _ (upperStarDerivedExtendScalarsCounit hρ ha e)
      ((e)^*[ModuleCat.{u + 1} Λ] ⋙
        Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctorCounit
      (HomotopyCategory.quasiIso _ (.up ℤ))
      (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
        (Iso.refl ((e)^*[ModuleCat.{u + 1} Λ] ⋙ Sheaf.extendScalars U.smallEtaleTopology ρ)) (.up ℤ))
        DerivedCategory.Qh).hom P
    simp only [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, NatTrans.comp_app,
      Functor.whiskerLeft_app, Category.assoc] at h
    exact h
  have hα (P : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ)) :
      (derivedExtendScalarsPullbackIsoOfCounit hρ ha e).symm.hom.app (DerivedCategory.Qh.obj P) ≫
        (Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctor.map
          (((e)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctorCounit.app P) ≫
        (Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctorCounit.app
          ((((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ)).obj P) =
      L((e)^*[ModuleCat.{u + 1} Λ']).map
          ((Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorCounit.app P) ≫
        ((e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctorCounit.app
          (((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
          (extendScalarsUpperStarIso ρ e).hom (.up ℤ)).app P) := by
    have h := Functor.leftDerivedNatTrans_app _ _ (derivedExtendScalarsUpperStarCounit hρ ha e)
      (upperStarDerivedExtendScalarsCounit hρ ha e) (HomotopyCategory.quasiIso _ (.up ℤ))
      (Functor.isoWhiskerRight (extendScalarsUpperStarHomotopyIso ρ e).symm
        DerivedCategory.Qh).inv P
    simp only [Functor.isoWhiskerRight_inv, Iso.symm_inv, Functor.whiskerRight_app,
      extendScalarsUpperStarHomotopyIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.mapHomotopyCategoryCompIso_refl_hom_app, Functor.mapHomotopyCategoryCompIso_refl_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] at h
    exact h
  have h := Functor.map_leftDerivedTensorComparison_comp_eq_of_counit_of_iso
    ((e)^*[ModuleCat.{u + 1} Λ]) (Sheaf.extendScalars U.smallEtaleTopology ρ)
    (Sheaf.extendScalars X.smallEtaleTopology ρ) ((e)^*[ModuleCat.{u + 1} Λ'])
    (extendScalarsUpperStarIso ρ e) (derivedExtendScalarsPullbackIsoOfCounit hρ ha e).symm γ.hom
    hα hγ K M
  rw [derivedExtendScalarsPullbackMap_eq]
  have h' := h =≫ ((derivedExtendScalarsPullbackIsoOfCounit hρ ha e).hom.app K ⊗ₘ
    (derivedExtendScalarsPullbackIsoOfCounit hρ ha e).hom.app M)
  simp only [Iso.symm_hom, Iso.symm_inv, Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    Iso.inv_hom_id_app] at h'
  erw [MonoidalCategory.id_tensorHom_id, Category.comp_id] at h'
  rw [derivedExtendScalarsMonoidal_δ, derivedExtendScalarsMonoidal_δ]
  exact h'.symm

end Tensor

end AlgebraicGeometry.Etale
