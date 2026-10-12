/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.VerdierDualLocal

/-!
# The Tor bound of the Verdier dual, by noetherian induction

Let `X` be separated of finite type over an algebraically closed field `k` with `dim X ≤ d`, and
`Λ` a finite ring whose exponent is invertible in `k`. If `K ∈ Dᵇc(X, Λ)` has Tor amplitude in
`[a, b]`, then `𝔻_X K = RHom(K, ω_X)` has Tor amplitude in `[-b - 2d, -a]`
(`AlgebraicGeometry.Etale.torAmplitudeIn_verdierDual_of_isAlgClosed`,
`lem-weil-verdier-preservation-strata`).

The proof is a noetherian induction on the support, along the localization triangles of the
*dualizing complex* `Ri_! Ri^! ω ⟶ ω ⟶ Rj_* j^* ω ⟶` for a closed immersion `i` with open
complement `j`, to which the triangulated functor `RHom(K, -)` is applied:

- `RHom(K, Ri_! Ri^! ω_Y) ≅ Ri_! 𝔻_Z(i^* K)`, handled by induction;
- `RHom(K, Rj_* j^* ω_Y) ≅ Rj_* 𝔻_U(j^* K)`; on a dense open `U` of the reduction of the support
  which is smooth of pure relative dimension `n ≤ d`, irreducible, and on which a flat model of
  `K` is lisse, `𝔻_U(j^* K)` has Tor amplitude `[-b - 2n, -a - 2n]`
  (`AlgebraicGeometry.Etale.exists_torAmplitudeIn_verdierDual_of_isFiniteLocallyConstantSheaf`),
  and the direct image `Rj_*` moves this to `[-b - 2n, -a]`
  (`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar`, `thm-sf-direct-image-tor-amplitude`).

Working with the localization triangles of `ω` rather than of `K` only uses the exactness of
the internal hom in its *second* variable.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-! ### Generalities -/

variable {Λ} in
/-- The Verdier dual only depends on the structure morphism. -/
lemma torAmplitudeIn_verdierDual_congr {X S : Scheme.{u}} {g₁ g₂ : X ⟶ S} (h : g₁ = g₂)
    [HasCompactification g₁] [HasCompactification g₂] {a b : ℤ} {K : DerivedCategoryModule Λ X}
    (hK : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      ((verdierDual (ModuleCat.{u + 1} Λ) g₁).obj (op K))) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      ((verdierDual (ModuleCat.{u + 1} Λ) g₂).obj (op K)) := by
  subst h
  exact hK

variable {Λ} in
/-- A zero object has every Tor amplitude. -/
lemma torAmplitudeIn_of_isZero {X : Scheme.{u}} {N : DerivedCategoryModule Λ X} (hN : IsZero N)
    (a b : ℤ) : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b N := fun _ ↦
  ⟨_root_.DerivedCategory.TStructure.t.isGE_of_isZero
      (isZero_derivedTensor_obj_obj_of_isZero_left hN _) a,
    _root_.DerivedCategory.TStructure.t.isLE_of_isZero
      (isZero_derivedTensor_obj_obj_of_isZero_left hN _) b⟩

variable {Λ} in
/-- The internal hom out of a zero object is zero. -/
lemma isZero_derivedHom_obj_obj_of_isZero {X : Scheme.{u}} {K : DerivedCategoryModule Λ X}
    (hK : IsZero K) (M : DerivedCategoryModule Λ X) :
    IsZero (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) K).homEquiv _ _).symm.injective
  exact (isZero_derivedTensor_obj_obj_of_isZero_left hK _).eq_of_src _ _

/-! ### The two pieces of the localization triangle of the dualizing complex -/

/-- **The closed piece.** For a closed immersion `i : Z ⟶ Y` and `K` on `Y`,
`RHom(K, Ri_! Ri^! ω_Y) ≅ Ri_! 𝔻_Z(i^* K)`; hence it has Tor amplitude in `[α, β]` as soon as
`𝔻_Z(i^* K)` does, the extension by zero along a closed immersion preserving Tor amplitude. -/
lemma torAmplitudeIn_derivedHom_rightDerivedLowerShriek_rightDerivedUpperShriek_dualizingComplex
    {Z Y S : Scheme.{u}} (aY : Y ⟶ S) [HasCompactification aY] (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasCompactification i] [HasCompactification (i ≫ aY)] [QuasiCompact (i ≫ aY)]
    (K : DerivedCategoryModule Λ Y) {α β : ℤ}
    (h : torAmplitudeIn (ModuleCat.{u + 1} Λ) Z α β
      ((verdierDual (ModuleCat.{u + 1} Λ) (i ≫ aY)).obj
        (op ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K)))) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) Y α β
      (((RHom(Y)[ModuleCat.{u + 1} Λ]).obj (op K)).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![ModuleCat.{u + 1} Λ]).obj (dualizingComplex _ aY)))) := by
  obtain ⟨eω⟩ := nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ i aY
  let eS := rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i
  let N := (R(i)^![ModuleCat.{u + 1} Λ]).obj (dualizingComplex _ aY)
  let e : ((RHom(Y)[ModuleCat.{u + 1} Λ]).obj (op K)).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj N) ≅
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((verdierDual (ModuleCat.{u + 1} Λ) (i ≫ aY)).obj
        (op ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K))) :=
    ((RHom(Y)[ModuleCat.{u + 1} Λ]).obj (op K)).mapIso (eS.app N) ≪≫
      (rightDerivedLowerStarCompDerivedHomIso Λ i K).app N ≪≫
      (eS.app _).symm ≪≫ (R(i)_![ModuleCat.{u + 1} Λ]).mapIso
        (((RHom(Z)[ModuleCat.{u + 1} Λ]).obj (op ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K))).mapIso
          eω)
  exact (torAmplitudeIn _ Y α β).prop_of_iso e.symm
    (torAmplitudeIn_rightDerivedLowerShriek_of_isClosedImmersion (ModuleCat.{u + 1} Λ) i
      (fun L ↦ hasProjectionFormula_of_finite Λ i _ L) h)

/-- **The open piece.** For a quasi-compact open immersion `j : U ⟶ Y` and `K` on `Y`,
`RHom(K, Rj_* j^* ω_Y) ≅ Rj_* 𝔻_U(j^* K)`. -/
theorem nonempty_iso_derivedHom_rightDerivedLowerStar_dualizingComplex {U Y S : Scheme.{u}}
    (aY : Y ⟶ S) [HasCompactification aY] (j : U ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    [HasCompactification j] [HasCompactification (j ≫ aY)] [QuasiCompact (j ≫ aY)]
    (K : DerivedCategoryModule Λ Y) :
    Nonempty (((RHom(Y)[ModuleCat.{u + 1} Λ]).obj (op K)).obj
        ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
          ((L((j)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex _ aY))) ≅
      (R((j)_*[ModuleCat.{u + 1} Λ])).obj ((verdierDual (ModuleCat.{u + 1} Λ) (j ≫ aY)).obj
        (op ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)))) := by
  obtain ⟨eω⟩ := nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ j aY
  exact ⟨(rightDerivedLowerStarCompDerivedHomIso Λ j K).app _ ≪≫
    (R((j)_*[ModuleCat.{u + 1} Λ])).mapIso
      (((RHom(U)[ModuleCat.{u + 1} Λ]).obj (op ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K))).mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory _ j).app _ ≪≫
          ((rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j).app _).symm ≪≫ eω))⟩

end Etale

end AlgebraicGeometry
