/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.DualizingComplexId
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!

# Global Verdier duality and the derived Poincaré pairing

Let `X` be smooth, proper and geometrically connected of pure relative dimension `d` over a
base `S`, with structure morphism `a_X : X ⟶ S`. Global Verdier duality is the case `Y = S`
of the Verdier-duality exchange `sk-thm-sf-verdier-exchange`: the coefficient dual of the
compactly supported cohomology of `K` is the ordinary cohomology of the Verdier dual of `K`,

`RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`.

Under an orientation `ω_X ≅ Λ(d)[2d]` the Verdier dual of a perfect `K` is `K^∨(d)[2d]`, and
global duality becomes the statement that the derived Poincaré pairing

`β_K : RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ`

is perfect: its tensor–internal-hom adjoint is an isomorphism.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_coefficientDual_rightDerivedLowerShriek`
  (`sk-thm-sf-global-duality`): `RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`.
- `AlgebraicGeometry.Etale.coefficientDualRightDerivedLowerShriekIso`
  (`sk-thm-sf-global-duality`): the same isomorphism, natural in `K`, for any coefficient
  category in which the projection formula holds.
- `AlgebraicGeometry.Etale.nonempty_iso_coefficientDual_rightDerivedLowerShriek_unit`
  (`sk-thm-sf-global-duality`): `RΓ_c(X, Λ)^∨ ≅ RΓ(X, ω_X)`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_coefficientDual_of_orientation`
  (`sk-thm-sf-identification`): under an orientation, `RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`.

## Implementation notes

`AlgebraicGeometry.Etale.rightDerivedGlobalSections` and
`AlgebraicGeometry.Etale.compactlySupportedGlobalSections` land in `D(A)`, the derived
category of the coefficient category, whereas the coefficient dual `(-)^∨` is a functor on
`D(S_ét)`. The statements below are therefore phrased one step earlier, with `Ra_{X*} K` and
`Ra_{X!} K` in `D(S_ét)`; applying `RΓ(S, -)` to them recovers the `RΓ` / `RΓ_c` form, since
`RΓ_c(X/S, -)` is by definition `RΓ(S, Ra_{X!} -)`.

The statements are made for a finite coefficient ring `Λ`, the finite stages of the blueprint.
Global duality is then the case `N = Λ_S` of the tensor–Hom exchange
`AlgebraicGeometry.Etale.nonempty_iso_derivedHom_rightDerivedLowerShriek`, which rests on the
projection formula at finite coefficients; it needs neither the properness, smoothness and
geometric connectedness of `X` nor the finiteness of `K` that the blueprint assumes, so these
hypotheses are not imposed. For a general coefficient category the projection formula, and
with it global duality, can fail.

The subject of `sk-thm-sf-identification` is the pairing `β_K` — the mixed-support cup
product followed by the evaluation `K ⊗ᴸ K^∨ ⟶ Λ_X` and the normalized trace — and the
assertion that its tensor–internal-hom adjoint is invertible. The pairing is
`AlgebraicGeometry.Etale.poincarePairing`, and its perfectness is proved next to it
(`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isDetecting` and, at finite
coefficients, `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing`); this file does not
import them, and records only the isomorphism that the blueprint identifies the adjoint of
`β_K` with. The blueprint's further assertion that the inverse of the adjoint *is* the global
duality isomorphism followed by `𝔻_X K ≅ K^∨(d)[2d]` is not stated: those isomorphisms are only
known to exist here (`Nonempty`), they are not constructed as specific maps.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

universe u'

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X S : Scheme.{u}} (aX : X ⟶ S) [HasCompactification aX] [(R(aX)_![A]).IsLeftAdjoint]

/-- The Verdier dual of the unit is the dualizing complex, `𝔻_X Λ_X = RHom(Λ_X, ω_X) ≅ ω_X`. -/
noncomputable def verdierDualObjUnitIso :
    (verdierDual A aX).obj (op (𝟙_ _)) ≅ dualizingComplex A aX :=
  (MonoidalClosed.unitNatIso.app _).symm

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- Blueprint `sk-thm-sf-global-duality`: Global Verdier duality, as a natural isomorphism.

If the projection formula holds for `a_X : X ⟶ S`, the coefficient dual of the compactly
supported direct image is the direct image of the Verdier dual, naturally in `K ∈ D(X_ét)`:

`(Ra_{X!} K)^∨ ≅ Ra_{X*} (𝔻_X K)`.

It is the tensor–Hom exchange `AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso`
evaluated at the unit `Λ_S`. Applying `RΓ(S, -)` gives `RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`. -/
noncomputable def coefficientDualRightDerivedLowerShriekIso [IsIso (projectionMap A aX)] :
    (R(aX)_![A]).op ⋙ DerivedCategory.coefficientDual A S ≅ verdierDual A aX ⋙ R((aX)_*[A]) :=
  (Functor.isoWhiskerRight (derivedHomRightDerivedLowerShriekIso A aX)
    ((CategoryTheory.evaluation _ _).obj (𝟙_ _))).symm

section Shift

variable {Z : Scheme.{u}}

attribute [local instance] Sheaf.monoidalCategory in
/-- Tensoring with a shifted complex shifts the tensor product, `K⟦a⟧ ⊗ᴸ M ≅ (K ⊗ᴸ M)⟦a⟧`,
naturally in `M`. -/
noncomputable def derivedTensorObjShiftIso
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) (a : ℤ) :
    (derivedTensor A Z).obj (K⟦a⟧) ≅ (derivedTensor A Z).obj K ⋙ shiftFunctor _ a :=
  NatIso.ofComponents (fun M ↦ (((derivedTensor A Z).flip.obj M).commShiftIso a).app K)
    (fun f ↦
      have : NatTrans.CommShift ((derivedTensor A Z).flip.map f) ℤ :=
        Functor.CommShift₂.commShift_flip_map (h := .int)
          (G := curriedTensor (_root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))) f
      (NatTrans.shift_app_comm ((derivedTensor A Z).flip.map f) a K).symm)

/-- The derived internal hom out of a shifted complex, `RHom(K⟦a⟧, M) ≅ RHom(K, M⟦-a⟧)`,
naturally in `M`: the conjugate of `K⟦a⟧ ⊗ᴸ - ≅ (K ⊗ᴸ -)⟦a⟧`. -/
noncomputable def derivedHomShiftIso
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) (a : ℤ) :
    (RHom(Z)[A]).obj (op (K⟦a⟧)) ≅ shiftFunctor _ (-a) ⋙ (RHom(Z)[A]).obj (op K) :=
  conjugateIsoEquiv (derivedTensorHomAdjunction A (K⟦a⟧))
    ((derivedTensorHomAdjunction A K).comp (shiftEquiv _ a).toAdjunction)
    (derivedTensorObjShiftIso A K a).symm

/-- The coefficient dual turns shifts into opposite shifts, `(K⟦a⟧)^∨ ≅ (K^∨)⟦-a⟧`. -/
noncomputable def coefficientDualShiftIso
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) (a : ℤ) :
    (DerivedCategory.coefficientDual A Z).obj (op (K⟦a⟧)) ≅
      ((DerivedCategory.coefficientDual A Z).obj (op K))⟦-a⟧ :=
  (derivedHomShiftIso A K a).app (𝟙_ _) ≪≫
    (((RHom(Z)[A]).obj (op K)).commShiftIso (-a)).app (𝟙_ _)

/-- Blueprint `sk-thm-sf-global-duality` (shifts): global duality for a shifted complex is the
shift of global duality, `RΓ_c(X, K⟦a⟧)^∨ ≅ RΓ(X, 𝔻_X K)⟦-a⟧`. It is the coefficient dual of the
commutation `Ra_{X!}(K⟦a⟧) ≅ (Ra_{X!} K)⟦a⟧`, then `(-)^∨` turning `⟦a⟧` into `⟦-a⟧`
(`AlgebraicGeometry.Etale.coefficientDualShiftIso`), then the shift of global duality for `K`.

This is only the object-level form of the shift compatibility: it does not state that this
isomorphism agrees with the shift of the global duality isomorphism for `K`, which the
blueprint also asks for. -/
noncomputable def coefficientDualRightDerivedLowerShriekShiftIso [IsIso (projectionMap A aX)]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) (a : ℤ) :
    (DerivedCategory.coefficientDual A S).obj (op ((R(aX)_![A]).obj (K⟦a⟧))) ≅
      ((R((aX)_*[A])).obj ((verdierDual A aX).obj (op K)))⟦-a⟧ :=
  ((DerivedCategory.coefficientDual A S).mapIso (((R(aX)_![A]).commShiftIso a).app K).op).symm ≪≫
    coefficientDualShiftIso A _ a ≪≫
      (shiftFunctor _ (-a)).mapIso ((coefficientDualRightDerivedLowerShriekIso A aX).app (op K))

end Shift

end General

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X S : Scheme.{u}} (aX : X ⟶ S)
  [HasCompactification aX]

/-- Blueprint `sk-thm-sf-global-duality`: Global Verdier duality.

For `a_X : X ⟶ S` admitting a compactification, a finite coefficient ring `Λ` and `K` an
object of `D(X_ét, Λ)`, the coefficient dual of the compactly supported cohomology of `K` is the
cohomology of the Verdier dual of `K`:

`RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`.

It is stated here for `Ra_{X!} K` and `Ra_{X*} (𝔻_X K)` in `D(S_ét)`; applying `RΓ(S, -)`
gives the displayed form, since `RΓ_c(X/S, -) = RΓ(S, Ra_{X!} -)`. It is the component at `K`
of the natural isomorphism `AlgebraicGeometry.Etale.coefficientDualRightDerivedLowerShriekIso`,
the tensor–Hom exchange `Ra_{X*} RHom(K, Ra_X^! N) ≅ RHom(Ra_{X!} K, N)` at `N = Λ_S`, the
projection formula holding at finite coefficients. -/
theorem nonempty_iso_coefficientDual_rightDerivedLowerShriek
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) S).obj
        (op ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K)) ≅
      (R((aX)_*[ModuleCat.{u + 1} Λ])).obj ((verdierDual (ModuleCat.{u + 1} Λ) aX).obj (op K))) :=
  have := isIso_projectionMap_of_finite Λ aX
  ⟨(coefficientDualRightDerivedLowerShriekIso (ModuleCat.{u + 1} Λ) aX).app (op K)⟩

/-- Blueprint `sk-thm-sf-global-duality`: Global Verdier duality for the constant coefficients.

For `K = Λ_X`, global duality reads `RΓ_c(X, Λ)^∨ ≅ RΓ(X, ω_X)`: here, one step earlier,
`(Ra_{X!} Λ_X)^∨ ≅ Ra_{X*} ω_X` in `D(S_ét)`, since `𝔻_X Λ_X = RHom(Λ_X, ω_X) ≅ ω_X`
(`AlgebraicGeometry.Etale.verdierDualObjUnitIso`). -/
theorem nonempty_iso_coefficientDual_rightDerivedLowerShriek_unit :
    Nonempty ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) S).obj
        (op ((R(aX)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _))) ≅
      (R((aX)_*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex (ModuleCat.{u + 1} Λ) aX)) :=
  (nonempty_iso_coefficientDual_rightDerivedLowerShriek Λ aX (𝟙_ _)).map fun e ↦
    e ≪≫ (R((aX)_*[ModuleCat.{u + 1} Λ])).mapIso (verdierDualObjUnitIso _ aX)

/-- Blueprint `sk-thm-sf-identification`: The derived Poincaré pairing is the duality
isomorphism.

With an orientation `o` of `a_X` of relative dimension `d` and with `K` perfect over `Λ_X`,
there is an isomorphism

`RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`,

again written one step earlier, with `Ra_{X*}` and `Ra_{X!}` in `D(S_ét)`. The blueprint
identifies this isomorphism with the tensor–internal-hom adjoint of the derived Poincaré
pairing `β_K`, and concludes that `β_K` is perfect; that perfectness is
`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isDetecting`. -/
theorem nonempty_iso_rightDerivedLowerStar_coefficientDual_of_orientation [HasTateTwist Λ]
    {d : ℕ} (o : Orientation Λ aX d)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hKperf : IsDualizable K) :
    Nonempty (((R((aX)_*[ModuleCat.{u + 1} Λ])).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
          ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K))).obj
            (tateObject Λ X d)))⟦(2 * d : ℤ)⟧ ≅
      (DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) S).obj
        (op ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K))) := by
  obtain ⟨e₁⟩ := nonempty_iso_coefficientDual_rightDerivedLowerShriek Λ aX K
  obtain ⟨e₂⟩ := Orientation.nonempty_iso_verdierDual_coefficientDual o hKperf
  exact ⟨((R((aX)_*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * d : ℤ)).symm.app _ ≪≫
    (R((aX)_*[ModuleCat.{u + 1} Λ])).mapIso ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K))).commShiftIso
        (2 * d : ℤ)).symm.app (tateObject Λ X d) ≪≫ e₂.symm) ≪≫ e₁.symm⟩

end Etale

end AlgebraicGeometry
