/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.ChartScalarReassociation
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.FiniteAffineTateScalarNormalization
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackIdentityNormalization
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarLineNormalizationOfBalancing
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientUnitCoherence

/-! # Scalar compatibility of expansion into the direct affine normal form

Source: Charts, retained Steps 4 and 10--11 of reduction-exceptional
(blueprint: lem-sp-finite-affine-scalar-expansion).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open WeilConjectures.PurityFiniteSetting
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
attribute [local implicit_reducible] affineTraceTower affineTraceProjection orderedAffineRight
  Scheme.finiteEtaleTateTwist FiniteSmoothPurity.ordinaryScalar derivedTensorRight

private theorem tensor_unit_square
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (δ : Functor.uncurry.obj (curriedTensor C) ⋙ F ≅
      F.prod F ⋙ Functor.uncurry.obj (curriedTensor D))
    (ι : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (hr : ∀ K : C, δ.hom.app (K, 𝟙_ C) ≫
      (F.obj K ◁ ι.hom) ≫ (ρ_ (F.obj K)).hom = F.map (ρ_ K).hom)
    {P K V : C} {P' V' : D} (a : P ⟶ K) (b : P' ⟶ F.obj K)
    (g : F.obj P ⟶ P') (v : F.obj V ⟶ V') (e : V ≅ 𝟙_ C) (e' : V' ≅ 𝟙_ D)
    (hg : g ≫ b = F.map a) (hv : v ≫ e'.hom = F.map e.hom ≫ ι.hom) :
    δ.hom.app (P, V) ≫ (g ⊗ₘ v) ≫ (b ⊗ₘ e'.hom) ≫ (ρ_ (F.obj K)).hom =
      F.map ((a ⊗ₘ e.hom) ≫ (ρ_ K).hom) := by
  have hn : F.map (a ⊗ₘ e.hom) ≫ δ.hom.app (K, 𝟙_ C) =
      δ.hom.app (P, V) ≫ (F.map a ⊗ₘ F.map e.hom) := by
    simpa only [Functor.comp_map, Functor.prod_map, Functor.prod_obj, Functor.uncurry_obj_map,
      curriedTensor_map_app, curriedTensor_obj_map, MonoidalCategory.tensorHom_def] using
      δ.hom.naturality (Prod.mkHom a e.hom)
  simp only [tensorHom_comp_tensorHom_assoc, hg, hv]
  have hcomp : (F.map a ⊗ₘ (F.map e.hom ≫ ι.hom)) =
      (F.map a ⊗ₘ F.map e.hom) ≫ (F.obj K ◁ ι.hom) := by
    rw [← MonoidalCategory.id_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
  rw [hcomp]
  simp only [Category.assoc]
  rw [← reassoc_of% hn, hr, ← F.map_comp]

private def zeroUnshiftedIso (R : Type (u + 1)) [CommRing R]
    (S : Scheme.{u}) (K : DerivedCategoryModule R S) :
    (ordinaryFinitePullback R (𝟙 S)).obj K ⊗
        ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ (Sheaf S.smallEtaleTopology
          (ModuleCat.{u + 1} R)))) ≅ K :=
  tensorIso ((leftDerivedUpperStarId (ModuleCat.{u + 1} R) S).app K)
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} R) S) ≪≫
    derivedTensorRightUnitor (ModuleCat.{u + 1} R) S K

private theorem expand_zero_inv (R : Type (u + 1)) [CommRing R]
    (N : ℕ) (hR : (N : R) = 0) (S : Scheme.{u}) (K : DerivedCategoryModule R S) :
    (finiteAffineExpandOrderedIso R N hR S 0).inv.app K =
      (shiftFunctor _ (0 : ℤ)).map (zeroUnshiftedIso R S K).hom ≫
        (shiftFunctorZero _ ℤ).hom.app K := by
  unfold finiteAffineExpandOrderedIso zeroUnshiftedIso
  simp only [Iso.symm_inv, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.comp_obj, Functor.leftUnitor_hom_app,
    Functor.comp_map, Functor.map_comp, Category.assoc,
    Functor.mapIso_hom, Iso.app_hom, tensorIso_hom, derivedTensorRightUnitorNatIso,
    NatIso.ofComponents_hom_app, derivedTensorRightUnitor_eq,
    derivedTensorRight, derivedTensorRightFunctor, Functor.flip_obj_map,
    Functor.flip_map_app, derivedTensor_map_app, derivedTensor_obj_map]
  erw [Category.id_comp, Category.id_comp]
  rw [← Functor.map_comp_assoc]
  simp only [← tensorHom_id, ← id_tensorHom]
  erw [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

private theorem unshifted_zero_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (K : DerivedCategoryModule A S) :
    (ExceptionalCoefficients.tensorIso φ S).hom.app
        ((ordinaryFinitePullback A (𝟙 S)).obj K,
          (DerivedCategory.singleFunctor _ 0).obj (𝟙_ (Sheaf S.smallEtaleTopology
            (ModuleCat.{u + 1} A)))) ≫
      derivedTensorHom (ModuleCat.{u + 1} B)
        ((scalarPullbackIso φ (𝟙 S)).inv.app K)
        (finiteAffineTateScalarMap φ S N hA hB 0) ≫
      (zeroUnshiftedIso B S ((scalarExtension φ S).obj K)).hom =
    (scalarExtension φ S).map (zeroUnshiftedIso A S K).hom := by
  have hb : finiteAffineTateScalarMap φ S N hA hB 0 ≫
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} B) S).hom =
    (scalarExtension φ S).map (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S).hom ≫
      (ExceptionalCoefficients.unitIso φ S).hom := by
    have hz := (finiteAffineTateScalar_normalization φ S N hN hA hB hS).2.1.1
    change finiteAffineTateScalarMap φ S N hA hB 0 = purityScalarUnitMap φ S at hz
    erw [hz]
    unfold purityScalarUnitMap purityTransportUnitMap
    simp only [Iso.symm_inv, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hi : (scalarPullbackIso φ (𝟙 S)).inv.app K ≫
      (leftDerivedUpperStarId (ModuleCat.{u + 1} B) S).hom.app
        ((scalarExtension φ S).obj K) =
    (scalarExtension φ S).map
      ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).hom.app K) := by
    rw [← (etaleScalarPullbackIdentityNormalization φ S).2.2 K,
      Iso.inv_hom_id_app_assoc]
  have hh := tensor_unit_square
    (V := (DerivedCategory.singleFunctor _ 0).obj
      (𝟙_ (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))))
    (V' := (DerivedCategory.singleFunctor _ 0).obj
      (𝟙_ (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B))))
    (scalarExtension φ S)
    (ExceptionalCoefficients.tensorIso φ S) (ExceptionalCoefficients.unitIso φ S)
    (ExceptionalCoefficients.tensorIso_right_unit φ S)
    ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).hom.app K)
    ((leftDerivedUpperStarId (ModuleCat.{u + 1} B) S).hom.app
      ((scalarExtension φ S).obj K))
    ((scalarPullbackIso φ (𝟙 S)).inv.app K)
    (finiteAffineTateScalarMap φ S N hA hB 0)
    (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S)
    (singleFunctorObjUnitIso (ModuleCat.{u + 1} B) S) hi hb
  simpa only [zeroUnshiftedIso, Iso.trans_hom, tensorIso_hom, derivedTensorRightUnitor_eq,
    derivedTensorHom, derivedTensor_map_app, derivedTensor_obj_map,
    MonoidalCategory.tensorHom_def, Functor.prod_obj, Functor.comp_obj,
    Functor.id_obj, Iso.app_hom, Scheme.finiteEtaleTateTwist, ordinaryFinitePullback,
    derivedTensor, curriedTensor_map_app, curriedTensor_obj_map, Category.assoc] using hh

/-- Expanding the ordered normal form commutes with its specified scalar map.
Source: Charts, canonical zero-coordinate units in retained Steps 4 and 10--11
(blueprint: lem-sp-finite-affine-scalar-expansion).

Proof: in positive dimension the expansion is the identity. At zero, write the
inverse expansion as the zero shift of the tensor of the identity-pullback and
single-unit comparisons, followed by the canonical zero-shift unitor. The normalized
scalar map on the zeroth Tate power is the scalar/unit comparison. Naturality of
the scalar tensorator and its right-unit law therefore commute scalar extension
through the unshifted tensor/unit composite; scalar/pullback identity normalization
supplies the first tensor factor. The scalar functor's canonical zero-shift law
and naturality of the zero-shift unitor complete the square. Cancel the two inverse
expansions to obtain the stated orientation. This holds for arbitrary derived
inputs and does not require a flat coefficient map. -/
theorem finiteAffineScalar_expansion
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (K : DerivedCategoryModule A S) :
    (scalarExtension φ (affineTraceTower S d)).map
        ((finiteAffineExpandOrderedIso A N hA S d).hom.app K) ≫
      finiteAffineNormalScalarMap φ N hA hB (affineTraceProjection S d)
        d (2 * (d : ℤ)) K =
    finiteAffineOrderedScalarMap φ N hA hB S d K ≫
      (finiteAffineExpandOrderedIso B N hB S d).hom.app ((scalarExtension φ S).obj K) := by
  cases d with
  | zero =>
    simp only [finiteAffineOrderedScalarMap, affineTraceTower, affineTraceProjection,
      Int.ofNat_zero]
    erw [Category.id_comp]
    change (scalarExtension φ S).map
        ((finiteAffineExpandOrderedIso A N hA S 0).hom.app K) ≫
        finiteAffineNormalScalarMap φ N hA hB (𝟙 S) 0 0 K =
      (finiteAffineExpandOrderedIso B N hB S 0).hom.app ((scalarExtension φ S).obj K)
    apply (cancel_epi ((scalarExtension φ S).map
      ((finiteAffineExpandOrderedIso A N hA S 0).inv.app K))).mp
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    apply (cancel_mono ((finiteAffineExpandOrderedIso B N hB S 0).inv.app
      ((scalarExtension φ S).obj K))).mp
    simp only [Category.assoc, Iso.hom_inv_id_app]
    rw [expand_zero_inv, expand_zero_inv]
    simp only [finiteAffineNormalScalarMap, Functor.map_comp, Category.assoc]
    let : (scalarExtension φ S).CommShift ℤ :=
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars S.smallEtaleTopology φ)).leftAdjointCommShift ℤ
    have hz := WeilConjectures.PurityFiniteSetting.zero_shift_map (scalarExtension φ S)
      ((scalarExtension φ S).map (zeroUnshiftedIso A S K).hom)
    have hs : FiniteSmoothPurity.scalarShiftIso φ S 0 =
        (scalarExtension φ S).commShiftIso 0 := rfl
    erw [Category.comp_id]
    erw [hs]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    simp only [Category.assoc]
    erw [unshifted_zero_square φ N hN hA hB S hS]
    erw [hz]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact ((shiftFunctorZero _ ℤ).hom.naturality (zeroUnshiftedIso A S K).hom).symm
  | succ d =>
    simp only [finiteAffineExpandOrderedIso, finiteAffineOrderedScalarMap,
      Iso.refl_hom, NatTrans.id_app, Category.comp_id]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]

end AlgebraicGeometry.Etale
