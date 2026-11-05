/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.GeometricFiber.Forget
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationLowerStar
public import WeilConjectures.WeilSheaf.ProperLowerStarAdjoint
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointCounitForget
public import WeilConjectures.CategoryTheory.Adjunction.MateIsIsoOfCounitPasting
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.SixFunctors.ProEtale.Adic.ProperLowerStarCondensedAdjoint

/-!
# Forgetting the Weil structure commutes with the proper direct image

Let `g : Z ⟶ Y` be a proper morphism of separated `k₀`-schemes of finite type and `ḡ` its base
change to the geometric fibres. Forgetting the Weil structures (`For`,
`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctor`) commutes with the
direct images: `For ∘ Rg_* ≅ Rḡ_* ∘ For`
(`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctorLowerStarIso`), the
inverse of the derived base change map of the condensed realization. Its mate
`For ∘ Rg^! ⟶ Rḡ^! ∘ For` is invertible for all right adjoints `Rg^!`, `Rḡ^!`
(`AlgebraicGeometry.WeilComplex.isIso_mateEquiv_geometricFiberBoundedConstructibleFunctorLowerStarIso`).

## Proof of the invertibility of the mate

Forgetting the Weil structures factors through the bounded constructible complexes of `ℓ`-adic
sheaves, `For = Φ ∘ U`, `Φ` the comparison of the two models. Along `U`, the counit of the right
adjoint `Rg^!` of Weil complexes lies over the counit of the right adjoint of the `ℓ`-adic `Rḡ_*`
(`CategoryTheory.Endofunctor.IsoAlgebra.exists_forget_map_counit_eq`), and `Φ` is an equivalence,
so the mate is invertible (`CategoryTheory.isIso_mateEquiv_app_of_counit_of_pasting`). The
derived base change map of the condensed realization is, through `For = Φ ∘ U`, the pasting of
the comparison of `U` with the direct images and of the comparison of `Φ` with the direct images
(`AlgebraicGeometry.ProEtaleWeilSheaf.mateEquiv_derivedCondensedRealizationUpperStarIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))] [IsProper g]

/-- **Forgetting the Weil structure commutes with the proper direct image**:
`For ∘ Rḡ_* ≅ Rg_* ∘ For`, the inverse of the derived base change map
`Rg_* ⋙ D(N_Y) ⟶ D(N_Z) ⋙ Rḡ_*` of the condensed realization (the mate of
`AlgebraicGeometry.ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso`), restricted to
Weil complexes. -/
noncomputable def geometricFiberBoundedConstructibleFunctorLowerStarIso :
    geometricFiberBoundedConstructibleFunctor k₀ l Z ⋙
        CondensedRing.boundedConstructibleLowerStar l (geometricFiberHom (k₀ := k₀) g) ≅
      derivedLowerStar g ⋙ geometricFiberBoundedConstructibleFunctor k₀ l Y :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (CondensedRing.boundedConstructibleLowerStarCompatibility l
          (geometricFiberHom (k₀ := k₀) g)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l Z) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (objectProperty k₀ l Z).ι
        (asIso (mateEquiv (ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l g)
          (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
            (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
          (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l g).hom).natTrans).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((objectProperty k₀ l Z).liftFullSubcategoryCompιIso (objectProperty k₀ l Y)
          (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor
          (objectProperty_rightDerivedLowerStar g)).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (derivedLowerStar g)
        (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l Y).symm ≪≫
      (Functor.associator _ _ _).symm)

variable (k₀ l) in
open scoped CategoryTheory.Obj in
/-- The comparison `D(AdicSheaf ℓ X̄) ≌ D(Mod_{Λ_X̄})` of the two models restricted to bounded
constructible complexes, on the geometric fibre of a separated `k₀`-scheme `X` of finite type
(as `AlgebraicGeometry.ProEtale.boundedConstructibleAdicEquivBoundedConstructible`, written with
the geometric fibre `X̄` itself rather than the source of its structure morphism over `k̄₀`). -/
noncomputable def geometricFiberBoundedConstructibleAdicEquiv (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    (DerivedCategory.boundedConstructibleAdic l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).FullSubcategory ≌
      BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
        (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left) where
  functor := (DerivedCategory.boundedConstructibleAdic l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).liftFullSubcategory _
    (adicSheafDerivedEquivCondensedMod l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor
    fun K hK ↦ (boundedConstructibleAdic_iff_boundedConstructible l k₀ (AlgebraicClosure k₀)
      (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure) K).1 hK
  inverse := ObjectProperty.liftFullSubcategory _ _
    (adicSheafDerivedEquivCondensedMod l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).inverse
    fun K hK ↦ (boundedConstructibleAdic_iff_boundedConstructible l k₀ (AlgebraicClosure k₀)
      (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure) _).2
      (ObjectProperty.prop_of_iso _ ((adicSheafDerivedEquivCondensedMod l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).counitIso.app K).symm hK)
  unitIso := NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _ ((adicSheafDerivedEquivCondensedMod l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).unitIso.app K.obj))
    fun f ↦ ObjectProperty.hom_ext _ ((adicSheafDerivedEquivCondensedMod l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).unit.naturality f.hom)
  counitIso := NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _ ((adicSheafDerivedEquivCondensedMod l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).counitIso.app K.obj))
    fun f ↦ ObjectProperty.hom_ext _ ((adicSheafDerivedEquivCondensedMod l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).counit.naturality f.hom)
  functor_unitIso_comp K := ObjectProperty.hom_ext _ ((adicSheafDerivedEquivCondensedMod l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor_unit_comp K.obj)

set_option maxHeartbeats 1000000 in
-- the derived categories of the three models are slow to elaborate
/-- **The mate of the forget comparison with the proper direct image is invertible**: for right
adjoints `Rg^!` of `Rg_*` on Weil complexes and `Rḡ^!` of `Rḡ_*` on bounded constructible
complexes, the mate `For ∘ Rg^! ⟶ Rḡ^! ∘ For` of
`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctorLowerStarIso` is an
isomorphism. -/
theorem isIso_mateEquiv_geometricFiberBoundedConstructibleFunctorLowerStarIso
    {R : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l Z} {R' : _ ⥤ _}
    (adj' : CondensedRing.boundedConstructibleLowerStar l (geometricFiberHom (k₀ := k₀) g) ⊣ R')
    (adj : derivedLowerStar g ⊣ R) (L : WeilComplex k₀ l Y) :
    IsIso ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _
      (geometricFiberBoundedConstructibleFunctorLowerStarIso g).hom)).natTrans.app L) := by
  let := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  let := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have hk := ringChar_algebraicClosure_ne (k₀ := k₀) (l := l)
  have : IsSeparated (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (IsSeparated (pullback.snd _ _))
  have hR (K : _root_.DerivedCategory (AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber))
      (hK : DerivedCategory.boundedConstructibleAdic l
        (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber K) :
      DerivedCategory.boundedConstructibleAdic l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber
        ((adicLowerStar l (Scheme.Hom.geometricFiberMap g
          (comp_over g (Spec (CommRingCat.of k₀))))).rightDerivedFunctor.obj K) :=
    boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure hk _ hK
  let T_A := (DerivedCategory.boundedConstructibleAdic l
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber).liftFullSubcategory
    (DerivedCategory.boundedConstructibleAdic l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (adicLowerStar l (Scheme.Hom.geometricFiberMap g
      (comp_over g (Spec (CommRingCat.of k₀))))).rightDerivedFunctor hR
  have : T_A.IsLeftAdjoint :=
    isLeftAdjoint_boundedConstructibleAdicRightDerivedLowerStar_of_isProper k₀ (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure hk _
  let adjA := Adjunction.ofIsLeftAdjoint T_A
  let U_Z := (objectProperty k₀ l Z).liftFullSubcategory
    (DerivedCategory.boundedConstructibleAdic l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (IsoAlgebra.forget _).mapDerivedCategory fun K hK ↦ (objectProperty_iff K).1 hK
  let U_Y := (objectProperty k₀ l Y).liftFullSubcategory
    (DerivedCategory.boundedConstructibleAdic l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (IsoAlgebra.forget _).mapDerivedCategory fun K hK ↦ (objectProperty_iff K).1 hK
  let EZ := geometricFiberBoundedConstructibleAdicEquiv k₀ l Z
  let EY := geometricFiberBoundedConstructibleAdicEquiv k₀ l Y
  let σ : derivedLowerStar g ⋙ U_Y ≅ U_Z ⋙ T_A := NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ ((IsoAlgebra.derivedForgetCommIso.{u + 1, u + 1, u + 2, u + 2}
      (adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g _))).app M.obj))
    fun f ↦ ObjectProperty.hom_ext _ ((IsoAlgebra.derivedForgetCommIso.{u + 1, u + 1, u + 2, u + 2}
      (adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g _))).hom.naturality f.hom)
  let ρ : T_A ⋙ EY.functor ≅ EZ.functor ⋙
      CondensedRing.boundedConstructibleLowerStar l (geometricFiberHom (k₀ := k₀) g) :=
    NatIso.ofComponents
      (fun K ↦ ObjectProperty.isoMk _ ((Functor.rightDerivedFunctorCommIso
        (adicLowerStarCompCondensedModIso l
          (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))).app K.obj))
      fun f ↦ ObjectProperty.hom_ext _ ((Functor.rightDerivedFunctorCommIso
        (adicLowerStarCompCondensedModIso l
          (Scheme.Hom.geometricFiberMap g
            (comp_over g (Spec (CommRingCat.of k₀)))))).hom.naturality f.hom)
  let eZ : geometricFiberBoundedConstructibleFunctor k₀ l Z ≅ U_Z ⋙ EZ.functor :=
    NatIso.ofComponents (fun M ↦ Iso.refl _) fun f ↦ by
      rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
  let eY : geometricFiberBoundedConstructibleFunctor k₀ l Y ≅ U_Y ⋙ EY.functor :=
    NatIso.ofComponents (fun M ↦ Iso.refl _) fun f ↦ by
      rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
  refine isIso_mateEquiv_app_of_counit_of_pasting_inv adj adjA adj' σ ρ eZ eY
    (geometricFiberBoundedConstructibleFunctorLowerStarIso g) ?_ ?_ ?_ L
  · intro M
    refine ObjectProperty.hom_ext _ ?_
    simp only [geometricFiberBoundedConstructibleFunctorLowerStarIso,
      Functor.FullyFaithful.preimageIso_inv, Functor.FullyFaithful.whiskeringRight_preimage_app,
      ObjectProperty.FullSubcategory.comp_hom, Iso.trans_inv, NatTrans.comp_app, Iso.symm_inv,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.comp_id]
    simp only [ObjectProperty.homMk_hom, geometricFiberBoundedConstructibleFunctorCompιIso,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.whiskerLeft_app, ObjectProperty.liftFullSubcategoryCompιIso, Iso.refl_hom,
      Iso.refl_inv, NatTrans.id_app, CondensedRing.boundedConstructibleLowerStarCompatibility,
      ObjectProperty.liftCompιIso, asIso_hom, Category.id_comp, Category.comp_id, Category.assoc,
      eY, eZ, σ, ρ, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
      ObjectProperty.isoMk_hom, ObjectProperty.FullSubcategory.id_hom, Iso.app_hom,
      ObjectProperty.liftFullSubcategory_map, ObjectProperty.liftFullSubcategory_obj_obj,
      ObjectProperty.lift_map, ObjectProperty.ι_obj, Over.homMk_left, EY, EZ,
      geometricFiberBoundedConstructibleAdicEquiv, CondensedRing.boundedConstructibleLowerStar,
      adicSheafDerivedEquivCondensedMod_functor]
    erw [Category.id_comp, Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id, CategoryTheory.Functor.map_id, Category.comp_id]
    erw [ProEtaleWeilSheaf.mateEquiv_derivedCondensedRealizationUpperStarIso_app' k₀ l g M.obj]
    rfl
  · intro L'
    obtain ⟨eH, heH⟩ := IsoAlgebra.exists_forget_map_counit_eq
      (adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g _))
      (DerivedCategory.boundedConstructibleAdic l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (DerivedCategory.boundedConstructibleAdic l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (fun _ hK ↦ hK.1) (fun K n hK ↦ ObjectProperty.le_shift _ n K hK)
      WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
      (fun K hK ↦
        (WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff K).2 hK)
      hR adjA (ProEtale.preservesColimit_discrete_rightDerivedFunctor_adicLowerStar _)
      (objectProperty k₀ l Z) (objectProperty k₀ l Y)
      (objectProperty_iff (X := Z)) (objectProperty_iff (X := Y))
      (objectProperty_rightDerivedLowerStar g) adj L'
    refine ⟨ObjectProperty.isoMk _ eH, ObjectProperty.hom_ext _ ?_⟩
    erw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom]
    exact heH
  · intro Y'
    have hu (M) : IsIso (EY.toAdjunction.unit.app M) := by
      rw [Equivalence.toAdjunction_unit]
      infer_instance
    have hu' (M) : IsIso (EZ.toAdjunction.unit.app M) := by
      rw [Equivalence.toAdjunction_unit]
      infer_instance
    have hc (M) : IsIso (EZ.toAdjunction.counit.app M) := by
      rw [Equivalence.toAdjunction_counit]
      infer_instance
    have h := Adjunction.isIso_mateEquiv_app_of_isIso adjA adj' ρ.symm EZ.toAdjunction
      EY.toAdjunction Y'
    rw [Iso.symm_hom] at h
    exact h

end AlgebraicGeometry.WeilComplex
