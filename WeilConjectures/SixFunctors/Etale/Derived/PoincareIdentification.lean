/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalVerdierDuality
public import WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing

/-!
# The adjoint of the Poincaré pairing is global Verdier duality

Let `a : X ⟶ Y` admit a compactification and satisfy the projection formula, and let
`γ : T[2d] ≅ Ra^! Λ_Y` be a purity isomorphism (for an orientation, `T = Λ_X(d)`). This file
identifies the tensor–internal-hom adjoint of the derived Poincaré pairing

`β_K^♯ : (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ (Ra_! K)^∨`

(over `Y = Spec k`: `RΓ(X, K^∨(d))[2d] ⟶ RΓ_c(X, K)^∨`) with the composite of the purity
identification `K^∨ ⊗ᴸ T[2d] ⟶ RHom(K, ω_X) = 𝔻_X K` and the inverse of the global
Verdier-duality isomorphism `(Ra_! K)^∨ ≅ Ra_* 𝔻_X K`. This is blueprint
`thm-pod-identification-of-the-comparison`.

## Main definitions

- `AlgebraicGeometry.Etale.exchangePairing`: the pairing
  `Ra_! M ⊗ᴸ Ra_* RHom(M, Ra^! N) ⟶ N` (cup product, evaluation, counit of `Ra_! ⊣ Ra^!`),
  whose adjoint is the tensor–Hom exchange.
- `AlgebraicGeometry.Etale.mixedSupportCupProductNatTrans`: the mixed-support cup product as a
  natural transformation in its second variable.
- `AlgebraicGeometry.Etale.purityVerdierDualMap`: the purity identification
  `(K^∨ ⊗ᴸ T)[2d] ⟶ 𝔻_X K` attached to `γ`.

## Main statements

- `AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso_hom_app_app`: the tensor–Hom
  exchange is the adjoint of `AlgebraicGeometry.Etale.exchangePairing`.
- `AlgebraicGeometry.Etale.isIso_purityVerdierDualMap`: the purity identification is an
  isomorphism for perfect `K`.
- `AlgebraicGeometry.Etale.curry_poincarePairing_eq` (`thm-pod-identification-of-the-comparison`):
  `β_K^♯` is the purity identification followed by the inverse of global Verdier duality.
- `AlgebraicGeometry.Etale.inv_curry_poincarePairing_eq`
  (`thm-pod-identification-of-the-comparison`): the inverse of `β_K^♯` is global Verdier duality
  followed by the inverse of the purity identification.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The derived category `D(X_ét, A)` of `A`-valued étale sheaves on `X`. -/
local notation "𝐃(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) A)

namespace Etale

variable {X Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a] [(R(a)_![A]).IsLeftAdjoint]

section CupProduct

/-- The mixed-support cup product `Ra_! K ⊗ᴸ Ra_* L ⟶ Ra_!(K ⊗ᴸ L)`
(`AlgebraicGeometry.Etale.mixedSupportCupProduct`) as a natural transformation in `L`. -/
noncomputable def mixedSupportCupProductNatTrans (K : 𝐃(X, A)) :
    R((a)_*[A]) ⋙ (derivedTensor A Y).obj ((R(a)_![A]).obj K) ⟶
      (derivedTensor A X).obj K ⋙ R(a)_![A] :=
  Functor.whiskerLeft R((a)_*[A])
      (((projectionMap A a).app K : (derivedTensor A Y).obj ((R(a)_![A]).obj K) ⟶
        L((a)^*[A]) ⋙ (derivedTensor A X).obj K ⋙ R(a)_![A])) ≫
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (derivedUpperStarLowerStarAdjunction A a).counit
        ((derivedTensor A X).obj K ⋙ R(a)_![A]) ≫ (Functor.leftUnitor _).hom

lemma mixedSupportCupProductNatTrans_app (K : 𝐃(X, A)) (L : 𝐃(X, A)) :
    (mixedSupportCupProductNatTrans A a K).app L = mixedSupportCupProduct A a K L := by
  simp [mixedSupportCupProductNatTrans, mixedSupportCupProduct]

/-- The mixed-support cup product is natural in its second variable. -/
@[reassoc]
lemma mixedSupportCupProduct_naturality (K : 𝐃(X, A)) {L L' : 𝐃(X, A)} (g : L ⟶ L') :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map ((R((a)_*[A])).map g) ≫
        mixedSupportCupProduct A a K L' =
      mixedSupportCupProduct A a K L ≫ (R(a)_![A]).map (((derivedTensor A X).obj K).map g) := by
  rw [← mixedSupportCupProductNatTrans_app, ← mixedSupportCupProductNatTrans_app]
  exact (mixedSupportCupProductNatTrans A a K).naturality g

/-- The mixed-support cup product commutes with the shifts in its second variable. -/
instance commShift_mixedSupportCupProductNatTrans (K : 𝐃(X, A)) :
    NatTrans.CommShift (mixedSupportCupProductNatTrans A a K) ℤ := by
  have := commShift_projectionMap_app A (f := a) K
  dsimp only [mixedSupportCupProductNatTrans]
  infer_instance

/-- The mixed-support cup product commutes with the shifts in its second variable,
componentwise: for `n : ℤ`,
```
Ra_! K ⊗ᴸ (Ra_* L)[n] ≅ (Ra_! K ⊗ᴸ Ra_* L)[n] --(⌣_c)[n]--> (Ra_!(K ⊗ᴸ L))[n] ≅ Ra_!((K ⊗ᴸ L)[n])
```
is `Ra_! K ⊗ᴸ (Ra_* L)[n] ≅ Ra_! K ⊗ᴸ Ra_*(L[n]) --⌣_c--> Ra_!(K ⊗ᴸ L[n]) ≅ Ra_!((K ⊗ᴸ L)[n])`.
-/
@[reassoc]
lemma commShiftIso_hom_app_comp_mixedSupportCupProduct_shift (K L : 𝐃(X, A)) (n : ℤ) :
    (((derivedTensor A Y).obj ((R(a)_![A]).obj K)).commShiftIso n).hom.app _ ≫
        (mixedSupportCupProduct A a K L)⟦n⟧' ≫ ((R(a)_![A]).commShiftIso n).inv.app _ =
      ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map
          (((R((a)_*[A])).commShiftIso n).inv.app L) ≫
        mixedSupportCupProduct A a K (L⟦n⟧) ≫
          (R(a)_![A]).map ((((derivedTensor A X).obj K).commShiftIso n).hom.app L) := by
  have h := NatTrans.shift_app_comm (mixedSupportCupProductNatTrans A a K) n L
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app,
    mixedSupportCupProductNatTrans_app, mixedSupportCupProductNatTrans_app] at h
  rw [← cancel_epi (((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map
    (((R((a)_*[A])).commShiftIso n).hom.app L)), ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp, reassoc_of% h]
  simp

end CupProduct

section Exchange

/-- The pairing of the tensor–Hom exchange,

`Ra_! M ⊗ᴸ Ra_* RHom(M, Ra^! N) ⟶ N`:

the mixed-support cup product, `Ra_!` of the evaluation `M ⊗ᴸ RHom(M, Ra^! N) ⟶ Ra^! N`, and
the counit of `Ra_! ⊣ Ra^!`. Its tensor–internal-hom adjoint is the tensor–Hom exchange
(`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso_hom_app_app`). -/
noncomputable def exchangePairing (M : 𝐃(X, A)) (N : 𝐃(Y, A)) :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj M)).obj
        ((R((a)_*[A])).obj ((RHom(X)[A].obj (op M)).obj ((R(a)^![A]).obj N))) ⟶ N :=
  mixedSupportCupProduct A a M _ ≫
    (R(a)_![A]).map ((derivedTensorHomAdjunction A M).counit.app _) ≫
      (rightDerivedUpperShriekAdjunction A a).counit.app N

/-- The tensor–Hom exchange `Ra_* RHom(M, Ra^! N) ⟶ RHom(Ra_! M, N)`
(`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso`) is the tensor–internal-hom
adjoint of the pairing `AlgebraicGeometry.Etale.exchangePairing`. -/
theorem derivedHomRightDerivedLowerShriekIso_hom_app_app [IsIso (projectionMap A a)]
    (M : 𝐃(X, A)) (N : 𝐃(Y, A)) :
    ((derivedHomRightDerivedLowerShriekIso A a).app (op M)).hom.app N =
      MonoidalClosed.curry (exchangePairing A a M N) := by
  rw [MonoidalClosed.eq_curry_iff, MonoidalClosed.uncurry_eq]
  have h := conjugateEquiv_counit
    (((derivedTensorHomAdjunction₂ A X).comp (derivedUpperStarLowerStarAdjunction A a)
      (rightDerivedUpperShriekAdjunction A a)).adj M)
    (((derivedTensorHomAdjunction₂ A Y).precomp R(a)_![A]).adj M)
    ((projectionMap A a).app M) N
  refine h.trans ?_
  simp [exchangePairing, mixedSupportCupProduct, Adjunction.comp_counit_app]

end Exchange

section Purity

variable {A} {d : ℕ} {T : 𝐃(X, A)}

/-- The purity identification `(K^∨ ⊗ᴸ T)[2d] ⟶ RHom(K, ω_X) = 𝔻_X K` of a purity isomorphism
`γ : T[2d] ≅ Ra^! Λ_Y = ω_X`: the tensor–internal-hom adjoint of
```
K ⊗ᴸ (K^∨ ⊗ᴸ T)[2d] ≅ (K ⊗ᴸ (K^∨ ⊗ᴸ T))[2d] --(twisted evaluation)[2d]--> T[2d] --γ--> ω_X.
```
For `T = Λ_X(d)` it is the identification `K^∨(d)[2d] ⟶ 𝔻_X K` of blueprint
`thm-sf-dual-perfect`; it is an isomorphism for perfect `K`
(`AlgebraicGeometry.Etale.isIso_purityVerdierDualMap`). -/
noncomputable def purityVerdierDualMap (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A a) (K : 𝐃(X, A)) :
    ((((derivedTensor A X).obj ((DerivedCategory.coefficientDual A X).obj (op K))).obj T)⟦
      (2 * d : ℤ)⟧) ⟶ (verdierDual A a).obj (op K) :=
  MonoidalClosed.curry ((((derivedTensor A X).obj K).commShiftIso (2 * d : ℤ)).hom.app _ ≫
    (twistedEvaluation T K)⟦(2 * d : ℤ)⟧' ≫ γ.hom)

/-- Blueprint `thm-sf-dual-perfect` (the identification used by
`thm-pod-identification-of-the-comparison`): for a perfect `K`, the purity identification
`(K^∨ ⊗ᴸ T)[2d] ⟶ 𝔻_X K` is an isomorphism. -/
theorem isIso_purityVerdierDualMap (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A a) {K : 𝐃(X, A)}
    (hK : IsDualizable K) : IsIso (purityVerdierDualMap a γ K) := by
  refine isIso_of_bijective_comp_shift (2 * d : ℤ) _ fun W ↦ ?_
  have e : (fun g : W⟦(2 * d : ℤ)⟧ ⟶ _ ↦ g ≫ purityVerdierDualMap a γ K) =
      MonoidalClosed.curry ∘
        (fun v ↦ (((derivedTensor A X).obj K).commShiftIso (2 * d : ℤ)).hom.app W ≫ v) ∘
          (fun z ↦ z ≫ γ.hom) ∘ (fun z ↦ z⟦(2 * d : ℤ)⟧') ∘
            (fun y ↦ ((derivedTensor A X).obj K).map y ≫ twistedEvaluation T K) ∘
              (fun g ↦ (shiftFunctor _ (2 * d : ℤ)).preimage g) := by
    funext g
    simp only [Function.comp_apply, purityVerdierDualMap]
    rw [← MonoidalClosed.curry_natural_left]
    congr 1
    obtain ⟨y, rfl⟩ := (shiftFunctor (𝐃(X, A)) (2 * d : ℤ)).map_surjective g
    rw [Functor.preimage_map, Functor.map_comp, Functor.commShiftIso_hom_naturality_assoc]
    simp
  rw [e]
  refine Function.Bijective.comp ⟨MonoidalClosed.curry_injective,
    fun g ↦ ⟨MonoidalClosed.uncurry g, MonoidalClosed.curry_uncurry g⟩⟩ ?_
  refine ((isIso_iff_coyoneda_map_bijective _).1 inferInstance _).comp ?_
  refine ((isIso_iff_yoneda_map_bijective _).1 inferInstance _).comp ?_
  refine Function.Bijective.comp ⟨(shiftFunctor _ _).map_injective,
    (shiftFunctor _ _).map_surjective⟩ ?_
  refine (bijective_derivedTensor_map_comp_twistedEvaluation A hK W).comp ?_
  exact ⟨fun g g' h ↦ (shiftFunctor _ (2 * d : ℤ)).map_injective (by simpa using h),
    fun y ↦ ⟨y⟦(2 * d : ℤ)⟧', by simp⟩⟩

end Purity

section Identification

variable {A} {d : ℕ} {T : 𝐃(X, A)} [IsIso (projectionMap A a)]

/-- Blueprint `thm-pod-identification-of-the-comparison`: Identification of the Poincaré pairing
with Verdier duality.

The tensor–internal-hom adjoint `β_K^♯ : (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ (Ra_! K)^∨` of the derived
Poincaré pairing `β_K` (`AlgebraicGeometry.Etale.poincarePairing`) of a purity isomorphism
`γ : T[2d] ≅ ω_X` is the composite
```
(Ra_*(K^∨ ⊗ᴸ T))[2d] ≅ Ra_*((K^∨ ⊗ᴸ T)[2d]) --Ra_*(purity)--> Ra_* 𝔻_X K --(global duality)⁻¹-->
  (Ra_! K)^∨
```
of the purity identification (`AlgebraicGeometry.Etale.purityVerdierDualMap`) and the inverse of
the global Verdier-duality isomorphism (`AlgebraicGeometry.Etale.globalVerdierDualityIso`).
Over `Y = Spec k` this is `RΓ(X, K^∨(d))[2d] ⟶ RΓ_c(X, K)^∨`. No hypothesis on `K` and no
properness of `a` is needed for this identity. -/
theorem curry_poincarePairing_eq (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A a) (K : 𝐃(X, A)) :
    MonoidalClosed.curry (poincarePairing a γ K) =
      ((R((a)_*[A])).commShiftIso (2 * d : ℤ)).inv.app _ ≫
        (R((a)_*[A])).map (purityVerdierDualMap a γ K) ≫
          (globalVerdierDualityIso A a K).inv := by
  rw [MonoidalClosed.curry_eq_iff, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_natural_left, globalVerdierDualityIso_inv,
    derivedHomRightDerivedLowerShriekIso_hom_app_app, MonoidalClosed.uncurry_curry,
    exchangePairing]
  change _ = ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map _ ≫
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map _ ≫ _
  rw [mixedSupportCupProduct_naturality_assoc, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc]
  have hu : ((derivedTensor A X).obj K).map (purityVerdierDualMap a γ K) ≫
      (derivedTensorHomAdjunction A K).counit.app (dualizingComplex A a) =
      (((derivedTensor A X).obj K).commShiftIso (2 * d : ℤ)).hom.app _ ≫
        (twistedEvaluation T K)⟦(2 * d : ℤ)⟧' ≫ γ.hom := by
    rw [purityVerdierDualMap, ← MonoidalClosed.uncurry_curry
      ((((derivedTensor A X).obj K).commShiftIso (2 * d : ℤ)).hom.app _ ≫
        (twistedEvaluation T K)⟦(2 * d : ℤ)⟧' ≫ γ.hom), MonoidalClosed.uncurry_eq,
      MonoidalClosed.curry_uncurry]
    rfl
  rw [hu, poincarePairing, poincarePairingEvaluation, smoothTrace]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.commShiftIso_inv_naturality_assoc,
    reassoc_of% commShiftIso_hom_app_comp_mixedSupportCupProduct_shift]

/-- Blueprint `thm-pod-identification-of-the-comparison`: Identification of the Poincaré pairing
with Verdier duality.

For `K` perfect over `Λ_X`, the tensor–internal-hom adjoint
`β_K^♯ : (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ (Ra_! K)^∨` of the derived Poincaré pairing is an isomorphism,
and its inverse is the global Verdier-duality isomorphism
`(Ra_! K)^∨ ≅ Ra_* 𝔻_X K` (`AlgebraicGeometry.Etale.globalVerdierDualityIso`) followed by the
inverse of the smooth-purity identification `𝔻_X K ≅ (K^∨ ⊗ᴸ T)[2d]`
(`AlgebraicGeometry.Etale.purityVerdierDualMap`, an isomorphism by
`AlgebraicGeometry.Etale.isIso_purityVerdierDualMap`) and the shift compatibility of `Ra_*`.
Over `Y = Spec k` this is `RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K) ≅ RΓ(X, K^∨(d))[2d]`. -/
theorem inv_curry_poincarePairing_eq (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A a) {K : 𝐃(X, A)}
    (hK : IsDualizable K) :
    haveI := isIso_purityVerdierDualMap a γ hK
    IsIso (MonoidalClosed.curry (poincarePairing a γ K)) ∧
      inv (MonoidalClosed.curry (poincarePairing a γ K)) =
        (globalVerdierDualityIso A a K).hom ≫
          (R((a)_*[A])).map (inv (purityVerdierDualMap a γ K)) ≫
            ((R((a)_*[A])).commShiftIso (2 * d : ℤ)).hom.app _ := by
  haveI := isIso_purityVerdierDualMap a γ hK
  have h := curry_poincarePairing_eq a γ K
  refine ⟨by rw [h]; infer_instance, ?_⟩
  rw [h]
  simp [← Functor.map_inv]

end Identification

end Etale

end AlgebraicGeometry
