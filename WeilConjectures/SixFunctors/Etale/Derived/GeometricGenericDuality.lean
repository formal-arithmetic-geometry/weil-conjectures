/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Rigid.ToIhomIhomTwist
public import WeilConjectures.EtaleCohomology.TateTwist.Normalized
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricGenericHom
public import WeilConjectures.SixFunctors.Etale.Derived.PointBiduality

/-!
# The double dual on a geometric generic fibre

For `p : X ⟶ 𝔸¹_k` with geometric generic fibre `g : X_η̄ ⟶ X`, `g^* ω_X ≅ ω_{X_η̄}(1)[2]`
Zariski locally on `X`, and `g^* δ_K` is an isomorphism if and only if `δ_{g^* K}` is
(`lem-weil-geometric-generic-duality`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

attribute [local instance] derivedBraidedCategory

/-- The double-dual morphism under a derived pullback `g : Z ⟶ Y` identifying the dualizing
complexes up to an invertible twist, `Lg^* ω_Y ≅ ω_Z ⊗ᴸ N` with `N` invertible: if the
comparison maps `Lg^* RHom(K, ω_Y) ⟶ RHom(Lg^* K, Lg^* ω_Y)` and
`Lg^* RHom(𝔻_Y K, ω_Y) ⟶ RHom(Lg^* 𝔻_Y K, Lg^* ω_Y)` are isomorphisms, then `Lg^* δ_K` is an
isomorphism if and only if `δ_{Lg^* K}` is. The twist `N` cancels in the double dual
(`CategoryTheory.MonoidalClosed.isIso_toIhomIhom_tensorObj_iff`). -/
theorem isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff_of_iso_tensorObj
    {Z Y S S' : Scheme.{u}} (g : Z ⟶ Y) (aY : Y ⟶ S) [HasCompactification aY]
    [(R(aY)_![A]).IsLeftAdjoint] (aZ : Z ⟶ S') [HasCompactification aZ]
    [(R(aZ)_![A]).IsLeftAdjoint] {N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)}
    (hN : IsInvertible N)
    (e : L((g)^*[A]).obj (dualizingComplex A aY) ≅ dualizingComplex A aZ ⊗ N)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (h₁ : letI := leftDerivedUpperStarMonoidal A g
      IsIso ((ihomComparison L((g)^*[A]) K).natTrans.app (dualizingComplex A aY)))
    (h₂ : letI := leftDerivedUpperStarMonoidal A g
      IsIso ((ihomComparison L((g)^*[A]) ((verdierDual A aY).obj (op K))).natTrans.app
        (dualizingComplex A aY))) :
    IsIso (L((g)^*[A]).map ((verdierDualDoubleDual A aY).app K)) ↔
      IsIso ((verdierDualDoubleDual A aZ).app (L((g)^*[A]).obj K)) := by
  let := leftDerivedUpperStarBraided A g
  have := h₁
  have := h₂
  exact (@isIso_map_toIhomIhom_iff _ _ _ _ _ _ _ _ _ _ L((g)^*[A]) _ (dualizingComplex A aY) K
    h₁ h₂).trans ((isIso_toIhomIhom_iff_of_iso e _).trans (isIso_toIhomIhom_tensorObj_iff _ _ hN))

end General

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]

section Duality

/-- The affine line `𝔸¹_k = Spec k[t]` over a field `k`. -/
local notation "𝔸¹" => Spec (CommRingCat.of (Polynomial k))

variable (k) in
/-- The geometric generic point `Spec \overline{k(t)} ⟶ 𝔸¹_k` of the affine line. -/
noncomputable def affineLineGeometricGenericPoint :
    Spec (.of (AlgebraicClosure (𝔸¹).functionField)) ⟶ 𝔸¹ :=
  Scheme.geometricGenericPoint _

variable (k) in
/-- The affine line `Spec k[t] ⟶ Spec k` is smooth of relative dimension one. -/
instance smoothOfRelativeDimension_one_specMap_algebraMap_polynomial :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) := by
  have := AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k))
  rw [Nat.card_unique] at this
  have h : Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1}).toRingHom) ≫
        (AffineSpace.SpecIso PUnit.{u + 1} (.of k)).inv ≫
          𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k) := by
    rw [AffineSpace.SpecIso_inv_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp
  rw [h, show 1 = 0 + (0 + 1) from rfl]
  infer_instance

variable {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a]
  [QuasiCompact a] [HasCompactification a] (p : X ⟶ 𝔸¹) [IsSeparated p] [LocallyOfFiniteType p]
  [QuasiCompact p]

/-- Blueprint `lem-weil-geometric-generic-duality`: The double dual on a geometric generic
fibre.

Let `X` be separated of finite type over `k`, let `p : X ⟶ 𝔸¹_k` be a `k`-morphism and let
`g : X_η̄ ⟶ X` be the pullback to the geometric generic fibre of `p`, with structure morphism
`a_η̄ : X_η̄ ⟶ η̄`. Then, Zariski locally on `X`, `g^* ω_X ≅ ω_{X_η̄}(1)[2]`: this holds as soon
as `X` is affine (apply it to the affine opens of a general `X`). -/
theorem nonempty_iso_leftDerivedUpperStar_dualizingComplex_geometricGenericPoint [IsAffine X]
    [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ]
    [HasCompactification (pullback.snd p (affineLineGeometricGenericPoint k))]
    (hp : p ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = a) :
    Nonempty ((L((pullback.fst p
        (affineLineGeometricGenericPoint k))^*[ModuleCat.{u + 1} Λ])).obj
          (dualizingComplex (ModuleCat.{u + 1} Λ) a) ≅
      (twistShift Λ _ 1).obj (dualizingComplex (ModuleCat.{u + 1} Λ)
        (pullback.snd p (affineLineGeometricGenericPoint k)))) :=
  sorry

set_option maxHeartbeats 1000000 in
-- unifying the categories of `δ_{g^* K}` and of `g^* K` unfolds the derived-category instances
/-- Blueprint `lem-weil-geometric-generic-duality`: The double dual on a geometric generic
fibre.

Let `X` be separated of finite type over `k`, let `p : X ⟶ 𝔸¹_k` be a `k`-morphism and let
`g : X_η̄ ⟶ X` be the pullback to the geometric generic fibre of `p`, with structure morphism
`a_η̄ : X_η̄ ⟶ η̄`. For every `K ∈ Dctf(X, Λ)`, the comparison `g^* ω_X ≅ ω_{X_η̄}(1)[2]`
identifies `g^* δ_K` with `δ_{g^* K}`, the invertible twist and shift cancelling in the double
dual: in particular `g^* δ_K` is an isomorphism if and only if `δ_{g^* K}` is. -/
theorem isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff_geometricGenericPoint
    [IsAffine X]
    [HasCompactification (pullback.snd p (affineLineGeometricGenericPoint k))]
    (hp : p ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = a)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((L((pullback.fst p (affineLineGeometricGenericPoint k))^*[ModuleCat.{u + 1} Λ])).map
        ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) a).app K)) ↔
      IsIso ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ)
        (pullback.snd p (affineLineGeometricGenericPoint k))).app
          ((L((pullback.fst p (affineLineGeometricGenericPoint k))^*[ModuleCat.{u + 1} Λ])).obj
            K)) := by
  haveI : NeZero (ringChar Λ) := ⟨CharP.ringChar_ne_zero_of_finite Λ⟩
  obtain ⟨e⟩ :=
    nonempty_iso_leftDerivedUpperStar_dualizingComplex_geometricGenericPoint Λ a p hp
  have hunit : constructibleFiniteTor (ModuleCat.{u + 1} Λ) (Spec (.of k)) (𝟙_ _) :=
    ⟨(boundedConstructible _ _).prop_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (boundedConstructible_singleFunctor_obj _ 0), 0, 0,
      (torAmplitudeIn _ _ 0 0).prop_of_iso
        (_root_.DerivedCategory.singleFunctorObjUnitIso _)
        (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
          (ObjectProperty.flat_of_isDualizable isDualizable_unit))⟩
  have hω := (constructibleFiniteTor_dualizingComplex Λ (𝟙 _) a hunit).1
  have hN := ((isInvertible_tateObject Λ (pullback p (affineLineGeometricGenericPoint k)) 1).shift
    (2 * 1)).of_iso (twistShiftConstantComplexIso Λ _ 1).symm
  exact isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff_of_iso_tensorObj _ _ a _ hN
    (e ≪≫ twistShiftObjIso Λ _ 1 _) K
    (isIso_ihomComparison_geometricGenericPoint Λ
      (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) p hK hω)
    (isIso_ihomComparison_geometricGenericPoint Λ
      (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) p
      (constructibleFiniteTor_verdierDual Λ a hK) hω)

end Duality

end Etale

end AlgebraicGeometry
