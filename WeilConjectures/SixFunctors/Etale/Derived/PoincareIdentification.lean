/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalVerdierDuality
public import WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing
public import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift

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
- `AlgebraicGeometry.Etale.projectionMapObjObj`: the components of the projection map, with
  source and target written through `Ra_!`, `-⊗ᴸ-` and `La^*`.
- `AlgebraicGeometry.Etale.purityVerdierDualMap`: the purity identification
  `(K^∨ ⊗ᴸ T)[2d] ⟶ 𝔻_X K` attached to `γ`.

## Main statements

- `AlgebraicGeometry.Etale.uncurry_derivedHomRightDerivedLowerShriekIso_hom_app_app`: the
  tensor–Hom exchange is the adjoint of `AlgebraicGeometry.Etale.exchangePairing`.
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
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

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

variable {X Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a]

section CupProduct
/-- The projection map `Ra_! K ⊗ᴸ - ⟶ Ra_!(K ⊗ᴸ La^* -)` (`AlgebraicGeometry.Etale.projectionMap`)
at `K`, as a natural transformation with target written as a composite of functors. -/
noncomputable def projectionMapComp (K : 𝐃(X, (ModuleCat.{u + 1} Λ))) :
    (derivedTensor (ModuleCat.{u + 1} Λ) Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj K) ⟶
      L((a)^*[ModuleCat.{u + 1} Λ]) ⋙ (derivedTensor (ModuleCat.{u + 1} Λ) X).obj K ⋙
          R(a)_![ModuleCat.{u + 1} Λ] :=
  (projectionMap (ModuleCat.{u + 1} Λ) a).app K

instance (K : 𝐃(X, A)) : NatTrans.CommShift (projectionMapComp A a K) ℤ :=
  commShift_projectionMap_app A (f := a) K

/-- The component `Ra_! K ⊗ᴸ M ⟶ Ra_!(K ⊗ᴸ La^* M)` of the projection map
(`AlgebraicGeometry.Etale.projectionMap`). -/
noncomputable def projectionMapObjObj (K : 𝐃(X, (ModuleCat.{u + 1} Λ))) (M : 𝐃(Y, (ModuleCat.{u + 1}
    Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)).obj M ⟶
      (R(a)_![ModuleCat.{u + 1} Λ]).obj (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj
          ((L((a)^*[ModuleCat.{u + 1} Λ])).obj M)) :=
  (projectionMapComp Λ a K).app M

omit [HasSmallSiteSheafify (ModuleCat.{u + 1} Λ)] in
@[reassoc]
lemma projectionMapApp_naturality (K : 𝐃(X, (ModuleCat.{u + 1} Λ))) {M M' : 𝐃(Y, (ModuleCat.{u + 1}
    Λ))} (g : M ⟶ M') :
    ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)).map g ≫
        projectionMapObjObj Λ a K M' =
      projectionMapObjObj Λ a K M ≫
        (R(a)_![ModuleCat.{u + 1} Λ]).map (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).map
            ((L((a)^*[ModuleCat.{u + 1} Λ])).map g)) :=
  (projectionMapComp Λ a K).naturality g

omit [HasSmallSiteSheafify (ModuleCat.{u + 1} Λ)] in
@[reassoc]
lemma projectionMapApp_shift (K : 𝐃(X, (ModuleCat.{u + 1} Λ))) (M : 𝐃(Y, (ModuleCat.{u + 1} Λ))) (n
    : ℤ) :
    (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj
        K)).commShiftIso n).hom.app M ≫
        (projectionMapObjObj Λ a K M)⟦n⟧' =
      projectionMapObjObj Λ a K (M⟦n⟧) ≫
        (R(a)_![ModuleCat.{u + 1} Λ]).map (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).map
          (((L((a)^*[ModuleCat.{u + 1} Λ])).commShiftIso n).hom.app M)) ≫
        (R(a)_![ModuleCat.{u + 1} Λ]).map ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
            K).commShiftIso n).hom.app
          ((L((a)^*[ModuleCat.{u + 1} Λ])).obj M)) ≫
        ((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso n).hom.app _ := by
  have h := NatTrans.shift_app_comm (projectionMapComp Λ a K) n M
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Functor.comp_map] at h
  exact h

omit [HasSmallSiteSheafify (ModuleCat.{u + 1} Λ)] in
@[reassoc]
lemma projectionMapApp_naturality_commShiftIso_inv (K L : 𝐃(X, (ModuleCat.{u + 1} Λ))) (n : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)).map
        (((R((a)_*[ModuleCat.{u + 1} Λ])).commShiftIso n).inv.app L) ≫
      projectionMapObjObj Λ a K ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (L⟦n⟧)) =
    projectionMapObjObj Λ a K (((R((a)_*[ModuleCat.{u + 1} Λ])).obj L)⟦n⟧) ≫
      (R(a)_![ModuleCat.{u + 1} Λ]).map (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).map
          ((L((a)^*[ModuleCat.{u + 1} Λ])).map
        (((R((a)_*[ModuleCat.{u + 1} Λ])).commShiftIso n).inv.app L))) :=
  projectionMapApp_naturality Λ a K _

omit [HasSmallSiteSheafify (ModuleCat.{u + 1} Λ)] in
lemma mixedSupportCupProduct_eq_projectionMapApp (K L : 𝐃(X, (ModuleCat.{u + 1} Λ))) :
    mixedSupportCupProduct Λ a K L =
      projectionMapObjObj Λ a K ((R((a)_*[ModuleCat.{u + 1} Λ])).obj L) ≫
        (R(a)_![ModuleCat.{u + 1} Λ]).map (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).counit.app L)) := by
  rw [mixedSupportCupProduct_eq]
  rfl

omit [HasSmallSiteSheafify (ModuleCat.{u + 1} Λ)] in
@[reassoc]
lemma commShiftIso_hom_app_comp_mixedSupportCupProduct_shift (K L : 𝐃(X, (ModuleCat.{u + 1} Λ))) (n
    : ℤ) :
    (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj
        K)).commShiftIso n).hom.app _ ≫
        (mixedSupportCupProduct Λ a K L)⟦n⟧' ≫ ((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso
            n).inv.app _ =
      ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)).map
          (((R((a)_*[ModuleCat.{u + 1} Λ])).commShiftIso n).inv.app L) ≫
        mixedSupportCupProduct Λ a K (L⟦n⟧) ≫
          (R(a)_![ModuleCat.{u + 1} Λ]).map ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
              K).commShiftIso n).hom.app L) := by
  rw [mixedSupportCupProduct_eq_projectionMapApp, mixedSupportCupProduct_eq_projectionMapApp]
  simp only [Category.assoc]
  rw [projectionMapApp_naturality_commShiftIso_inv_assoc, Functor.map_comp, Category.assoc,
    projectionMapApp_shift_assoc]
  congr 1
  rw [← Functor.commShiftIso_hom_naturality_assoc]
  simp only [Functor.id_obj, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  simp only [← Functor.map_comp]
  congr 1
  rw [← Functor.commShiftIso_hom_naturality, Adjunction.shift_counit_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

end CupProduct

section Exchange

/-- The pairing of the tensor–Hom exchange,

`Ra_! M ⊗ᴸ Ra_* RHom(M, Ra^! N) ⟶ N`:

the mixed-support cup product, `Ra_!` of the evaluation `M ⊗ᴸ RHom(M, Ra^! N) ⟶ Ra^! N`, and
the counit of `Ra_! ⊣ Ra^!`. Its tensor–internal-hom adjoint is the tensor–Hom exchange
(`AlgebraicGeometry.Etale.uncurry_derivedHomRightDerivedLowerShriekIso_hom_app_app`). -/
noncomputable def exchangePairing (M : 𝐃(X, (ModuleCat.{u + 1} Λ))) (N : 𝐃(Y, (ModuleCat.{u + 1}
    Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj M)).obj
        ((R((a)_*[ModuleCat.{u + 1} Λ])).obj ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op M)).obj
            ((R(a)^![Λ]).obj N))) ⟶ N :=
  mixedSupportCupProduct Λ a M _ ≫
    (R(a)_![ModuleCat.{u + 1} Λ]).map ((derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ)
        M).counit.app _) ≫
      (rightDerivedUpperShriekAdjunction Λ a).counit.app N

omit [HasSmallSiteSheafify (ModuleCat.{u + 1} Λ)] in
/-- The tensor–Hom exchange `Ra_* RHom(M, Ra^! N) ⟶ RHom(Ra_! M, N)`
(`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso`) is the tensor–internal-hom
adjoint of the pairing `AlgebraicGeometry.Etale.exchangePairing`. -/
theorem uncurry_derivedHomRightDerivedLowerShriekIso_hom_app_app [IsIso (projectionMap (ModuleCat.{u
    + 1} Λ) a)]
    (M : 𝐃(X, (ModuleCat.{u + 1} Λ))) (N : 𝐃(Y, (ModuleCat.{u + 1} Λ))) :
    MonoidalClosed.uncurry (((derivedHomRightDerivedLowerShriekIso Λ a).app (op M)).hom.app N) =
      exchangePairing Λ a M N := by
  obtain ⟨e, he, hPF⟩ : ∃ e, derivedHomRightDerivedLowerShriekIso Λ a =
      ((derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} Λ) X).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a)
        (rightDerivedUpperShriekAdjunction Λ a)).conjugateIso
        ((derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} Λ) Y).precomp R(a)_![ModuleCat.{u + 1} Λ])
            e ∧
      ∀ M' L', (e.hom.app M').app L' = projectionMapObjObj Λ a M' L' :=
    ⟨_, rfl, fun _ _ ↦ rfl⟩
  rw [he]
  refine (MonoidalClosed.uncurry_eq _).trans
    ((ParametrizedAdjunction.map_conjugateIso_app_hom_app_comp_counit _ _ e (op M) N).trans ?_)
  rw [hPF, exchangePairing, mixedSupportCupProduct_eq_projectionMapApp]
  simp only [ParametrizedAdjunction.comp_adj, Adjunction.comp_counit_app, Category.assoc]
  rfl

end Exchange

section Purity

variable {A} {Λ} {d : ℕ} {T : 𝐃(X, A)}

/-- The purity identification `(K^∨ ⊗ᴸ T)[2d] ⟶ RHom(K, ω_X) = 𝔻_X K` of a purity isomorphism
`γ : T[2d] ≅ Ra^! Λ_Y = ω_X`: the tensor–internal-hom adjoint of
```
K ⊗ᴸ (K^∨ ⊗ᴸ T)[2d] ≅ (K ⊗ᴸ (K^∨ ⊗ᴸ T))[2d] --(twisted evaluation)[2d]--> T[2d] --γ--> ω_X.
```
For `T = Λ_X(d)` it is the identification `K^∨(d)[2d] ⟶ 𝔻_X K` of blueprint
`thm-sf-dual-perfect`; it is an isomorphism for perfect `K`
(`AlgebraicGeometry.Etale.isIso_purityVerdierDualMap`). -/
noncomputable def purityVerdierDualMap (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ a) (K : 𝐃(X,
    (ModuleCat.{u + 1} Λ))) :
    ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj ((DerivedCategory.coefficientDual (ModuleCat.{u +
        1} Λ) X).obj (op K))).obj T)⟦
      (2 * d : ℤ)⟧) ⟶ (verdierDual Λ a).obj (op K) :=
  MonoidalClosed.curry ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).commShiftIso (2 * d :
      ℤ)).hom.app _ ≫
    (twistedEvaluation T K)⟦(2 * d : ℤ)⟧' ≫ γ.hom)

omit [HasSmallSiteSheafify (ModuleCat.{u + 1} Λ)] [Etale.UpperStarPreservesFlat (ModuleCat.{u + 1}
    Λ)] in
/-- Blueprint `thm-sf-dual-perfect` (the identification used by
`thm-pod-identification-of-the-comparison`): for a perfect `K`, the purity identification
`(K^∨ ⊗ᴸ T)[2d] ⟶ 𝔻_X K` is an isomorphism. -/
theorem isIso_purityVerdierDualMap (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ a) {K : 𝐃(X,
    (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) : IsIso (purityVerdierDualMap a γ K) := by
  refine isIso_of_bijective_comp_shift (2 * d : ℤ) _ fun W ↦ ?_
  have e : (fun g : W⟦(2 * d : ℤ)⟧ ⟶ _ ↦ g ≫ purityVerdierDualMap a γ K) =
      MonoidalClosed.curry ∘
        (fun v ↦ (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).commShiftIso (2 * d : ℤ)).hom.app
            W ≫ v) ∘
          (fun z ↦ z ≫ γ.hom) ∘ (fun z ↦ z⟦(2 * d : ℤ)⟧') ∘
            (fun y ↦ ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).map y ≫ twistedEvaluation T K)
                ∘
              (fun g ↦ (shiftFunctor _ (2 * d : ℤ)).preimage g) := by
    funext g
    simp only [Function.comp_apply, purityVerdierDualMap]
    refine (MonoidalClosed.curry_natural_left _ _).symm.trans ?_
    congr 1
    obtain ⟨y, rfl⟩ := (shiftFunctor (𝐃(X, (ModuleCat.{u + 1} Λ))) (2 * d : ℤ)).map_surjective g
    rw [Functor.preimage_map]
    change ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).map (y⟦(2 * d : ℤ)⟧') ≫ _ = _
    rw [Functor.commShiftIso_hom_naturality_assoc]
    simp
  rw [e]
  refine Function.Bijective.comp ⟨MonoidalClosed.curry_injective,
    fun g ↦ ⟨MonoidalClosed.uncurry g, MonoidalClosed.curry_uncurry g⟩⟩ ?_
  refine ((isIso_iff_coyoneda_map_bijective _).1 inferInstance _).comp ?_
  refine ((isIso_iff_yoneda_map_bijective _).1 inferInstance _).comp ?_
  refine Function.Bijective.comp ⟨(shiftFunctor _ _).map_injective,
    (shiftFunctor _ _).map_surjective⟩ ?_
  refine (bijective_derivedTensor_map_comp_twistedEvaluation Λ hK W).comp ?_
  exact ⟨fun g g' h ↦ by simpa using congrArg (shiftFunctor _ (2 * d : ℤ)).map h,
    fun y ↦ ⟨y⟦(2 * d : ℤ)⟧', by simp⟩⟩

end Purity

section Identification

variable {A} {Λ} {d : ℕ} {T : 𝐃(X, A)} [IsIso (projectionMap A a)]

omit [HasSmallSiteSheafify A]

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
theorem curry_poincarePairing_eq (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ a) (K : 𝐃(X, (ModuleCat.{u
    + 1} Λ))) :
    MonoidalClosed.curry (poincarePairing a γ K) =
      ((R((a)_*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * d : ℤ)).inv.app _ ≫
        (R((a)_*[ModuleCat.{u + 1} Λ])).map (purityVerdierDualMap a γ K) ≫
          (globalVerdierDualityIso Λ a K).inv := by
  refine (MonoidalClosed.curry_eq_iff _ _).2
    (Eq.symm ((MonoidalClosed.uncurry_natural_left _ _).trans ?_))
  erw [MonoidalClosed.uncurry_natural_left]
  rw [globalVerdierDualityIso_inv]
  erw [uncurry_derivedHomRightDerivedLowerShriekIso_hom_app_app]
  rw [exchangePairing]
  symm
  change _ = ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)).map
      _ ≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)).map _ ≫ _
  erw [reassoc_of% (mixedSupportCupProduct_naturality_right Λ a K (purityVerdierDualMap a γ K))]
  have hu : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).map (purityVerdierDualMap a γ K) ≫
      (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) K).counit.app (dualizingComplex Λ a) =
      (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).commShiftIso (2 * d : ℤ)).hom.app _ ≫
        (twistedEvaluation T K)⟦(2 * d : ℤ)⟧' ≫ γ.hom := by
    exact (MonoidalClosed.uncurry_eq _).symm.trans (MonoidalClosed.uncurry_curry _)
  have hu' : (R(a)_![ModuleCat.{u + 1} Λ]).map (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).map
      (purityVerdierDualMap a γ K)) ≫
      (R(a)_![ModuleCat.{u + 1} Λ]).map ((derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ)
          K).counit.app (dualizingComplex Λ a)) =
      (R(a)_![ModuleCat.{u + 1} Λ]).map ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
          K).commShiftIso (2 * d : ℤ)).hom.app _) ≫
        (R(a)_![ModuleCat.{u + 1} Λ]).map ((twistedEvaluation T K)⟦(2 * d : ℤ)⟧') ≫
            (R(a)_![ModuleCat.{u + 1} Λ]).map γ.hom := by
    refine (Functor.map_comp _ _ _).symm.trans ((congrArg (R(a)_![ModuleCat.{u + 1} Λ]).map
        hu).trans ?_)
    simp only [Functor.map_comp]
  erw [reassoc_of% hu']
  rw [poincarePairing, poincarePairingEvaluation, smoothTrace]
  simp only [Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_inv_naturality_assoc,
    reassoc_of% commShiftIso_hom_app_comp_mixedSupportCupProduct_shift]

/-- Blueprint `thm-pod-identification-of-the-comparison`: Identification of the Poincaré pairing
with Verdier duality.

For `K` perfect over `Λ_X`, the tensor–internal-hom adjoint
`β_K^♯ : (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ (Ra_! K)^∨` of the derived Poincaré pairing is an isomorphism:
by `AlgebraicGeometry.Etale.curry_poincarePairing_eq` it is a composite of isomorphisms, the
purity identification being one by `AlgebraicGeometry.Etale.isIso_purityVerdierDualMap`. -/
theorem isIso_curry_poincarePairing (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ a) {K : 𝐃(X,
    (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) : IsIso (MonoidalClosed.curry (poincarePairing a γ K)) := by
  have := isIso_purityVerdierDualMap a γ hK
  rw [curry_poincarePairing_eq]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
    (@IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _) (Iso.isIso_inv _))

/-- Blueprint `thm-pod-identification-of-the-comparison`: Identification of the Poincaré pairing
with Verdier duality.

For `K` perfect over `Λ_X`, the inverse of the isomorphism
`β_K^♯ : (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ (Ra_! K)^∨`
(`AlgebraicGeometry.Etale.isIso_curry_poincarePairing`) is the global Verdier-duality
isomorphism `(Ra_! K)^∨ ≅ Ra_* 𝔻_X K` (`AlgebraicGeometry.Etale.globalVerdierDualityIso`)
followed by the inverse of the smooth-purity identification `𝔻_X K ≅ (K^∨ ⊗ᴸ T)[2d]` and the
shift compatibility of `Ra_*`. Over `Y = Spec k` this is
`RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K) ≅ RΓ(X, K^∨(d))[2d]`. -/
theorem inv_curry_poincarePairing_eq (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ a) {K : 𝐃(X,
    (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) :
    haveI := isIso_curry_poincarePairing a γ hK
    haveI := isIso_purityVerdierDualMap a γ hK
    inv (MonoidalClosed.curry (poincarePairing a γ K)) =
      (globalVerdierDualityIso Λ a K).hom ≫
        (R((a)_*[ModuleCat.{u + 1} Λ])).map (inv (purityVerdierDualMap a γ K)) ≫
          ((R((a)_*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * d : ℤ)).hom.app _ := by
  have := isIso_curry_poincarePairing a γ hK
  have := isIso_purityVerdierDualMap a γ hK
  refine IsIso.inv_eq_of_hom_inv_id ?_
  have hE := ((((R((a)_*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * d : ℤ)).app _).symm ≪≫
    (R((a)_*[ModuleCat.{u + 1} Λ])).mapIso (asIso (purityVerdierDualMap a γ K)) ≪≫
      (globalVerdierDualityIso Λ a K).symm).hom_inv_id
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, asIso_hom, asIso_inv, Iso.app_hom, Iso.app_inv, Category.assoc] at hE
  rw [curry_poincarePairing_eq]
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_)
  exact hE

end Identification

end Etale

end AlgebraicGeometry
