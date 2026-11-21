/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.HomShift
public import WeilConjectures.SixFunctors.Etale.Derived.Identity
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!

# Global Verdier duality and the derived Poincaré pairing

Let `X` be smooth, proper and geometrically connected of pure relative dimension `d` over a
base `S`, with structure morphism `a_X : X ⟶ S`. Global Verdier duality is the case `Y = S`
of the Verdier-duality exchange formulas: the coefficient dual of
the compactly supported cohomology of `K` is the ordinary cohomology of the Verdier dual of `K`,

`RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`.

Under an orientation `ω_X ≅ Λ(d)[2d]` the Verdier dual of a perfect `K` is `K^∨(d)[2d]`, and
global duality becomes the statement that the derived Poincaré pairing

`β_K : RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ`

is perfect: its tensor–internal-hom adjoint is an isomorphism.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_coefficientDual_rightDerivedLowerShriek`:
  `RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`.
- `AlgebraicGeometry.Etale.coefficientDualRightDerivedLowerShriekIso`: the same isomorphism,
  natural in `K`, for any coefficient category in which the projection formula holds.
- `AlgebraicGeometry.Etale.nonempty_iso_coefficientDual_rightDerivedLowerShriek_unit`:
  `RΓ_c(X, Λ)^∨ ≅ RΓ(X, ω_X)`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_coefficientDual_of_orientation`:
  under an orientation, `RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`.

## Implementation details

`AlgebraicGeometry.Etale.rightDerivedGlobalSections` and
`AlgebraicGeometry.Etale.compactlySupportedGlobalSections` land in `D(A)`, the derived
category of the coefficient category, whereas the coefficient dual `(-)^∨` is a functor on
`D(S_ét)`. The statements below are therefore phrased one step earlier, with `Ra_{X*} K` and
`Ra_{X!} K` in `D(S_ét)`; applying `RΓ(S, -)` to them recovers the `RΓ` / `RΓ_c` form, since
`RΓ_c(X/S, -)` is by definition `RΓ(S, Ra_{X!} -)`.

The statements are made for a finite coefficient ring `Λ`, where the projection formula holds.
They need neither the properness, smoothness and geometric connectedness of `X` nor the
finiteness of `K`, so these hypotheses are not imposed. For a general coefficient category the
projection formula, and with it global duality, can fail.

The Poincaré pairing `β_K` and its perfectness are
`AlgebraicGeometry.Etale.poincarePairing` and
`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isDetecting`; this file only records
the isomorphism with which the adjoint of `β_K` is identified. That the inverse of the adjoint is
the global duality isomorphism followed by `𝔻_X K ≅ K^∨(d)[2d]` is not stated, since those
isomorphisms are only known to exist here (`Nonempty`).
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
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {X S : Scheme.{u}} (aX : X ⟶ S) [HasCompactification aX]

/-- The Verdier dual of the unit is the dualizing complex, `𝔻_X Λ_X = RHom(Λ_X, ω_X) ≅ ω_X`. -/
noncomputable def verdierDualObjUnitIso :
    (verdierDual Λ aX).obj (op (𝟙_ _)) ≅ dualizingComplex Λ aX :=
  (MonoidalClosed.unitNatIso.app _).symm

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- Global Verdier duality as a natural isomorphism for an arbitrary right adjoint `G` of
`Ra_{X!}`: `(Ra_{X!} K)^∨ ≅ Ra_{X*} RHom(K, G Λ_S)`, for a general coefficient category. -/
noncomputable def coefficientDualRightDerivedLowerShriekIsoOfAdjunction
    {G : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (adj : R(aX)_![A] ⊣ G)
    [IsIso (projectionMap A aX)] :
    (R(aX)_![A]).op ⋙ DerivedCategory.coefficientDual A S ≅
        (RHom(X)[A]).flip.obj (G.obj (𝟙_ _)) ⋙ R((aX)_*[A]) :=
  (Functor.isoWhiskerRight (derivedHomLowerShriekIsoOfAdjunction A aX adj)
    ((CategoryTheory.evaluation _ _).obj (𝟙_ _))).symm

/-- Global Verdier duality, as a natural isomorphism.

If the projection formula holds for `a_X : X ⟶ S`, the coefficient dual of the compactly
supported direct image is the direct image of the Verdier dual, naturally in `K ∈ D(X_ét)`:

`(Ra_{X!} K)^∨ ≅ Ra_{X*} (𝔻_X K)`.

Over `S = Spec k` this is `RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`, natural in `K`. -/
noncomputable def coefficientDualRightDerivedLowerShriekIso
    [IsIso (projectionMap (ModuleCat.{u + 1} Λ) aX)] :
    (R(aX)_![ModuleCat.{u + 1} Λ]).op ⋙ DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) S ≅
        verdierDual Λ aX ⋙ R((aX)_*[ModuleCat.{u + 1} Λ]) :=
  coefficientDualRightDerivedLowerShriekIsoOfAdjunction (ModuleCat.{u + 1} Λ) aX
    (rightDerivedUpperShriekAdjunction Λ aX)

/-- **Global Verdier duality is the tensor–Hom exchange at the unit**: the component of
`coefficientDualRightDerivedLowerShriekIso` at `K` is the component at `K` and `Λ_S` of the
exchange `Ra_{X*} RHom(K, Ra_X^! N) ≅ RHom(Ra_{X!} K, N)`
(`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso`), read backwards. -/
theorem coefficientDualRightDerivedLowerShriekIso_hom_app
    [IsIso (projectionMap (ModuleCat.{u + 1} Λ) aX)]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (coefficientDualRightDerivedLowerShriekIso Λ aX).hom.app (op K) =
      ((derivedHomRightDerivedLowerShriekIso Λ aX).app (op K)).inv.app (𝟙_ _) :=
  rfl

section Shift

variable {Z : Scheme.{u}}

/-- The coefficient dual turns shifts into opposite shifts, `(K⟦a⟧)^∨ ≅ (K^∨)⟦-a⟧`. -/
noncomputable def coefficientDualShiftIso
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ) :
    (DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) Z).obj (op (K⟦a⟧)) ≅
      ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) Z).obj (op K))⟦-a⟧ :=
  (derivedHomShiftIso (ModuleCat.{u + 1} Λ) K a).app (𝟙_ _)

/-- Global Verdier duality and shifts: global duality for a shifted complex is the shift of
global duality,
`RΓ_c(X, K⟦a⟧)^∨ ≅ RΓ(X, 𝔻_X K)⟦-a⟧`. -/
noncomputable def coefficientDualRightDerivedLowerShriekShiftIso [IsIso (projectionMap (ModuleCat.{u
    + 1} Λ) aX)]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ) :
    (DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) S).obj (op ((R(aX)_![ModuleCat.{u + 1}
        Λ]).obj (K⟦a⟧))) ≅
      ((R((aX)_*[ModuleCat.{u + 1} Λ])).obj ((verdierDual Λ aX).obj (op K)))⟦-a⟧ :=
  ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) S).mapIso (((R(aX)_![ModuleCat.{u + 1}
      Λ]).commShiftIso a).app K).op).symm ≪≫
    coefficientDualShiftIso Λ _ a ≪≫
      (shiftFunctor _ (-a)).mapIso ((coefficientDualRightDerivedLowerShriekIso Λ aX).app (op K))

end Shift

end General

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X S : Scheme.{u}} (aX : X ⟶ S)
  [HasCompactification aX]

/-- **Global Verdier duality.**

For `a_X : X ⟶ S` admitting a compactification, a finite coefficient ring `Λ` and `K` an
object of `D(X_ét, Λ)`, the coefficient dual of the compactly supported cohomology of `K` is the
cohomology of the Verdier dual of `K`:

`RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`.

It is stated here for `Ra_{X!} K` and `Ra_{X*} (𝔻_X K)` in `D(S_ét)`. -/
theorem nonempty_iso_coefficientDual_rightDerivedLowerShriek
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) S).obj
        (op ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K)) ≅
      (R((aX)_*[ModuleCat.{u + 1} Λ])).obj ((verdierDual Λ aX).obj (op K))) :=
  have := isIso_projectionMap_of_finite Λ aX
  ⟨(coefficientDualRightDerivedLowerShriekIso Λ aX).app (op K)⟩

/-- **Global Verdier duality for the constant coefficients**: `RΓ_c(X, Λ)^∨ ≅ RΓ(X, ω_X)`,
stated as `(Ra_{X!} Λ_X)^∨ ≅ Ra_{X*} ω_X` in `D(S_ét)`. -/
theorem nonempty_iso_coefficientDual_rightDerivedLowerShriek_unit :
    Nonempty ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) S).obj
        (op ((R(aX)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _))) ≅
      (R((aX)_*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ aX)) :=
  (nonempty_iso_coefficientDual_rightDerivedLowerShriek Λ aX (𝟙_ _)).map fun e ↦
    e ≪≫ (R((aX)_*[ModuleCat.{u + 1} Λ])).mapIso (verdierDualObjUnitIso _ aX)

/-- **Global Verdier duality, in the point category.**

Let `k` be a separably closed field, `s = Spec k`, `a_X : X ⟶ s` admitting a compactification
(for instance separated of finite type, smooth or not, proper or not) and `Λ` a finite
coefficient ring. For `K ∈ D(X_ét, Λ)` there is an isomorphism of `Λ`-module complexes

`RΓ_c(X, K)^∨ = RHom_Λ(RΓ_c(X, K), Λ) ≅ RΓ(X, 𝔻_X K)`. -/
theorem nonempty_iso_ihom_compactlySupportedGlobalSections_verdierDual {k : Type u} [Field k]
    [IsSepClosed k] (aX : X ⟶ Spec (.of k)) [HasCompactification aX]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((ihom ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K)).obj
        (𝟙_ _) ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj
        ((verdierDual Λ aX).obj (op K))) := by
  have := isIso_projectionMap_of_finite Λ aX
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedGlobalSections_coefficientDual_of_isEquivalence
    (ModuleCat.{u + 1} Λ) (Spec (.of k)) ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K)
  exact ⟨e₁.symm ≪≫ (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).mapIso
      ((coefficientDualRightDerivedLowerShriekIso Λ aX).app (op K)) ≪≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ) aX).app _⟩

/-- **Global duality under an orientation.**

With an orientation `o` of `a_X` of relative dimension `d` and with `K` perfect over `Λ_X`,
there is an isomorphism

`RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`,

again written with `Ra_{X*}` and `Ra_{X!}` in `D(S_ét)`. -/
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
