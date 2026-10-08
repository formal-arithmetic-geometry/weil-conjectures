/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.Monoidal.Closed.ProjectionPairing
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
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
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_coefficientDual_of_orientation`
  (`sk-thm-sf-identification`): under an orientation, `RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`,
  from global duality and `𝔻_X K ≅ K^∨(d)[2d]`.
- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isDetecting`
  (`thm-sf-identification`): the derived Poincaré pairing `β_K` of a perfect `K` is perfect,
  provided the projection formula holds at a class of test objects detecting isomorphisms.
- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_hasProjectionFormula`
  (`thm-sf-identification`): the same with all objects as test objects.
- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isSepClosed`
  (`sk-thm-sf-identification`): over a separably closed field, `β_K` is perfect in the point
  category as soon as the projection formula holds at the shifts `Λ_s[r]`, which detect
  isomorphisms there (`lem-sf-detection`).

## Implementation notes

`AlgebraicGeometry.Etale.rightDerivedGlobalSections` and
`AlgebraicGeometry.Etale.compactlySupportedGlobalSections` land in `D(A)`, the derived
category of the coefficient category, whereas the coefficient dual `(-)^∨` is a functor on
`D(S_ét)`. The statements below are therefore phrased one step earlier, with `Ra_{X*} K` and
`Ra_{X!} K` in `D(S_ét)`; applying `RΓ(S, -)` to them recovers the `RΓ` / `RΓ_c` form, since
`RΓ_c(X/S, -)` is by definition `RΓ(S, Ra_{X!} -)`.

The blueprint assumes *either* that `X` is proper *or* that `X = X₀ ×_{k₀} k` for a smooth
separated geometrically connected finite-type scheme `X₀` over a finite field. The second
alternative needs the model datum `X₀`, which this repository does not yet have, so only the
proper case is stated here. `[IsProper a_X]` also supplies `[HasCompactification a_X]`, hence
separatedness and finite type.

The subject of `sk-thm-sf-identification` is the pairing `β_K` — the mixed-support cup
product followed by the evaluation `K ⊗ᴸ K^∨ ⟶ Λ_X` and the normalized trace
(`AlgebraicGeometry.Etale.poincarePairing`) — and the assertion that its tensor–internal-hom
adjoint is invertible. The projection formula is an axiom of the blueprint's six-functor datum;
in this repository it is the property `AlgebraicGeometry.Etale.HasProjectionFormula` of the
projection map, which the perfectness statements take as a hypothesis at the test objects.
The blueprint's further assertion that the inverse of the adjoint *is* the global duality
isomorphism followed by `𝔻_X K ≅ K^∨(d)[2d]` is not stated: those isomorphisms are only known
to exist here (`Nonempty`), they are not constructed as specific maps.

The proof of perfectness is the formal Yoneda argument of the blueprint, isolated in
`CategoryTheory.MonoidalClosed.isIso_curry_of_projection`. It is applied to `β_K` by
unification after unfolding the definition of `β_K`, so that the kernel never has to compare
`β_K` with a re-elaborated copy of it (such comparisons time out).

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
  [HasSmallSiteSheafify A]

namespace Etale

section GlobalDuality

variable {X S : Scheme.{u}} (aX : X ⟶ S) [IsProper aX] (d : ℕ)
  [SmoothOfRelativeDimension d aX] [GeometricallyConnected aX]

/-- Blueprint `sk-thm-sf-global-duality`: Global Verdier duality.

For `X` smooth, proper and geometrically connected of pure relative dimension `d` over `S`,
and `K` an object of `Dctf(X, A)`, the coefficient dual of the compactly supported cohomology
of `K` is the cohomology of the Verdier dual of `K`:

`RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`.

It is stated here for `Ra_{X!} K` and `Ra_{X*} (𝔻_X K)` in `D(S_ét)`; applying `RΓ(S, -)`
gives the displayed form, since `RΓ_c(X/S, -) = RΓ(S, Ra_{X!} -)`. -/
theorem nonempty_iso_coefficientDual_rightDerivedLowerShriek
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K) :
    Nonempty ((DerivedCategory.coefficientDual A S).obj (op ((R(aX)_![A]).obj K)) ≅
      (R((aX)_*[A])).obj ((verdierDual A aX).obj (op K))) :=
  sorry

omit [SmoothOfRelativeDimension d aX] in
/-- Blueprint `sk-thm-sf-identification`: The derived Poincaré pairing is the duality
isomorphism.

Under the hypotheses of `sk-thm-sf-global-duality`, with an orientation `o` of `a_X` of
relative dimension `d` and with `K` perfect over `Λ_X`, there is an isomorphism

`RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`,

again written one step earlier, with `Ra_{X*}` and `Ra_{X!}` in `D(S_ét)`. The blueprint
identifies this isomorphism with the tensor–internal-hom adjoint of the derived Poincaré
pairing `β_K`, and concludes that `β_K` is perfect; that perfectness is
`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isDetecting`. -/
theorem nonempty_iso_rightDerivedLowerStar_coefficientDual_of_orientation
    [SmoothOfRelativeDimension d aX] (o : Orientation A aX d)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K) (hKperf : IsDualizable K) :
    Nonempty (((R((aX)_*[A])).obj
        ((DerivedCategory.coefficientDual A X).obj (op K) ⊗ o.twist))⟦(2 * d : ℤ)⟧ ≅
      (DerivedCategory.coefficientDual A S).obj (op ((R(aX)_![A]).obj K))) := by
  obtain ⟨e₁⟩ := nonempty_iso_coefficientDual_rightDerivedLowerShriek A aX hK
  obtain ⟨e₂⟩ := Orientation.nonempty_iso_verdierDual_coefficientDual A aX o hKperf
  exact ⟨((R((aX)_*[A])).commShiftIso (2 * d : ℤ)).symm.app _ ≪≫
    (R((aX)_*[A])).mapIso ((((derivedTensor A X).obj
      ((DerivedCategory.coefficientDual A X).obj (op K))).commShiftIso (2 * d : ℤ)).symm.app
        o.twist ≪≫ e₂.symm) ≪≫ e₁.symm⟩

end GlobalDuality

section Perfectness

variable [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable {X Y : Scheme.{u}}

omit [ConcreteCategory A FA] [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] in
/-- For a perfect `K`, the twisted evaluation `K ⊗ᴸ (K^∨ ⊗ᴸ T) ⟶ T` is a counit: every map
`K ⊗ᴸ Z ⟶ T` factors uniquely as `K ⊗ᴸ y` followed by the twisted evaluation, for a map
`y : Z ⟶ K^∨ ⊗ᴸ T`. In other words `K^∨ ⊗ᴸ T` is the internal hom `RHom(K, T)`. -/
theorem bijective_derivedTensor_map_comp_twistedEvaluation
    {T K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsDualizable K)
    (Z : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Function.Bijective (fun y : Z ⟶ ((derivedTensor A X).obj
        ((DerivedCategory.coefficientDual A X).obj (op K))).obj T ↦
      ((derivedTensor A X).obj K).map y ≫ twistedEvaluation T K) := by
  obtain ⟨_⟩ := hK
  obtain ⟨_⟩ := DerivedCategory.nonempty_exactPairing_swap K Kᘁ
  have hi : IsIso (MonoidalClosed.ihomUnitTensorToIhom K T) :=
    MonoidalClosed.isIso_ihomUnitTensorToIhom Kᘁ K T
  have ht : twistedEvaluation T K =
      MonoidalClosed.uncurry (MonoidalClosed.ihomUnitTensorToIhom K T) := by
    rw [MonoidalClosed.ihomUnitTensorToIhom, MonoidalClosed.uncurry_curry]
    rfl
  have he : (fun y : Z ⟶ ((derivedTensor A X).obj
        ((DerivedCategory.coefficientDual A X).obj (op K))).obj T ↦
      ((derivedTensor A X).obj K).map y ≫ twistedEvaluation T K) =
      MonoidalClosed.uncurry ∘ (fun y ↦ y ≫ MonoidalClosed.ihomUnitTensorToIhom K T) := by
    funext y
    rw [ht]
    exact (MonoidalClosed.uncurry_natural_left _ _).symm
  rw [he]
  exact Function.Bijective.comp ⟨MonoidalClosed.uncurry_injective,
    fun g ↦ ⟨MonoidalClosed.curry g, MonoidalClosed.uncurry_curry g⟩⟩
    ((isIso_iff_yoneda_map_bijective _).1 hi _)

variable (a : X ⟶ Y) [HasCompactification a] {d : ℕ}

omit [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A] in
/-- The adjoint description of the evaluation part of the derived Poincaré pairing: for `K`
perfect and any `N`, maps `h : N ⟶ Ra_*(K^∨ ⊗ᴸ T)` correspond bijectively to maps
`K ⊗ᴸ La^* N ⟶ T`, through `K ⊗ᴸ La^* h`, `K ⊗ᴸ` the counit of `La^* ⊣ Ra_*` and the twisted
evaluation. -/
theorem bijective_derivedTensor_map_comp_counit_comp_twistedEvaluation (o : Orientation A a d)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsDualizable K)
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    Function.Bijective (fun h : N ⟶ (R((a)_*[A])).obj (((derivedTensor A X).obj
        ((DerivedCategory.coefficientDual A X).obj (op K))).obj o.twist) ↦
      ((derivedTensor A X).obj K).map ((L((a)^*[A])).map h) ≫
        ((derivedTensor A X).obj K).map ((derivedUpperStarLowerStarAdjunction A a).counit.app _) ≫
          twistedEvaluation o.twist K) := by
  have e : (fun h : N ⟶ (R((a)_*[A])).obj (((derivedTensor A X).obj
        ((DerivedCategory.coefficientDual A X).obj (op K))).obj o.twist) ↦
      ((derivedTensor A X).obj K).map ((L((a)^*[A])).map h) ≫
        ((derivedTensor A X).obj K).map ((derivedUpperStarLowerStarAdjunction A a).counit.app _) ≫
          twistedEvaluation o.twist K) =
      (fun y ↦ ((derivedTensor A X).obj K).map y ≫ twistedEvaluation o.twist K) ∘
        ((derivedUpperStarLowerStarAdjunction A a).homEquiv _ _).symm := by
    funext h
    simp [Adjunction.homEquiv_counit]
  rw [e]
  exact (bijective_derivedTensor_map_comp_twistedEvaluation A hK _).comp (Equiv.bijective _)

omit [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A] in
/-- The trace part of the derived Poincaré pairing is a counit: maps `z : U ⟶ T` correspond
bijectively to maps `Ra_!(U[2d]) ⟶ Λ_Y`, through `Ra_!(z[2d])` followed by the smooth trace
`Tr_o`. This is the adjunction `Ra_! ⊣ Ra^!` read through `T[2d] ≅ Ra^! Λ_Y`. -/
theorem bijective_rightDerivedLowerShriek_map_shift_comp_smoothTrace (o : Orientation A a d)
    (e : (L((a)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _)
    (U : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Function.Bijective (fun z : U ⟶ o.twist ↦ (R(a)_![A]).map (z⟦(2 * d : ℤ)⟧') ≫
      smoothTrace o e) := by
  have e' : (fun z : U ⟶ o.twist ↦ (R(a)_![A]).map (z⟦(2 * d : ℤ)⟧') ≫ smoothTrace o e) =
      ((rightDerivedUpperShriekAdjunction A a).homEquiv _ _).symm ∘
        (fun z' ↦ z' ≫ (o.dualizingComplexIso e).hom) ∘ (fun z ↦ z⟦(2 * d : ℤ)⟧') := by
    funext z
    simp only [Function.comp_apply, Adjunction.homEquiv_counit, smoothTrace, Functor.map_comp,
      Category.assoc]
  rw [e']
  exact (Equiv.bijective _).comp (((isIso_iff_yoneda_map_bijective _).1 inferInstance _).comp
    ⟨(shiftFunctor _ _).map_injective, (shiftFunctor _ _).map_surjective⟩)

omit [HasSmallSiteSheafify A] in
/-- Blueprint `thm-sf-identification`: the pairing is the duality isomorphism.

**The derived Poincaré pairing is perfect.** Let `a : X ⟶ Y` admit a compactification, let `o`
be an orientation of `a` of relative dimension `d` with twist `T`, and let `K` be perfect over
`Λ_X`. If the projection map `Ra_! K ⊗ᴸ N ⟶ Ra_!(K ⊗ᴸ La^* N)` is an isomorphism at every test
object `N` of a class `S` detecting isomorphisms after the shift by `2d`, then the derived
Poincaré pairing `β_K : Ra_! K ⊗ᴸ (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ Λ_Y`
(`AlgebraicGeometry.Etale.poincarePairing`) is perfect: its tensor–internal-hom adjoint
`(Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ (Ra_! K)^∨` is an isomorphism.

Over `Y = Spec k` this is `RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`. Following the blueprint, the
adjoint is identified on test objects `N[2d]` with the chain of bijections
```
(N ⟶ Ra_*(K^∨ ⊗ᴸ T)) ≃ (La^* N ⟶ K^∨ ⊗ᴸ T) ≃ (K ⊗ᴸ La^* N ⟶ T) ≃ ((K ⊗ᴸ La^* N)[2d] ⟶ Ra^! Λ_Y)
  ≃ (Ra_!(K ⊗ᴸ La^* N)[2d] ⟶ Λ_Y) ≃ ((Ra_! K ⊗ᴸ N)[2d] ⟶ Λ_Y) ≃ (N[2d] ⟶ (Ra_! K)^∨)
```
given by the adjunctions `La^* ⊣ Ra_*`, `K ⊗ᴸ - ⊣ K^∨ ⊗ᴸ -`, `Ra_! ⊣ Ra^!`, the orientation
`T[2d] ≅ Ra^! Λ_Y` and the projection formula; see
`CategoryTheory.MonoidalClosed.isIso_curry_of_projection`. -/
theorem isPerfectPairing_poincarePairing_of_isDetecting (o : Orientation A a d)
    (e : (L((a)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsDualizable K)
    (S : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A) → Prop)
    (hS : ∀ ⦃P Q : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)⦄ (u : P ⟶ Q),
      (∀ N, S N → Function.Bijective (fun g : N⟦(2 * d : ℤ)⟧ ⟶ P ↦ g ≫ u)) → IsIso u)
    (hPF : ∀ N, S N → HasProjectionFormula A a K N) :
    IsPerfectPairing (poincarePairing a o e K) := by
  constructor
  rw [poincarePairing, poincarePairingEvaluation, mixedSupportCupProduct]
  exact MonoidalClosed.isIso_curry_of_projection _ _ _ _ _ _ _ _ _ S hS hPF
    (bijective_derivedTensor_map_comp_counit_comp_twistedEvaluation A a o hK)
    (bijective_rightDerivedLowerShriek_map_shift_comp_smoothTrace A a o e)

omit [HasSmallSiteSheafify A] in
/-- Blueprint `thm-sf-identification`: the pairing is the duality isomorphism.

The derived Poincaré pairing of a perfect `K` is perfect whenever the projection formula
holds for `a` at `K` and every object of `D(Y_ét)`
(`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isDetecting` with all objects as
test objects). -/
theorem isPerfectPairing_poincarePairing_of_hasProjectionFormula (o : Orientation A a d)
    (e : (L((a)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsDualizable K)
    (hPF : ∀ N, HasProjectionFormula A a K N) :
    IsPerfectPairing (poincarePairing a o e K) :=
  isPerfectPairing_poincarePairing_of_isDetecting A a o e hK (fun _ ↦ True)
    (fun _ _ u hu ↦ isIso_of_bijective_comp_shift (2 * d : ℤ) u fun N ↦ hu N trivial)
    (fun N _ ↦ hPF N)

end Perfectness

section Point

variable {k : Type u} [Field k] [IsSepClosed k] {Λ : Type (u + 1)} [CommRing Λ]
  {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [HasCompactification a] {d : ℕ}

/-- Blueprint `sk-thm-sf-identification`: The derived Poincaré pairing is the duality
isomorphism.

**The derived Poincaré pairing is perfect in the point category.** Let `k` be separably closed,
`a : X ⟶ Spec k` admit a compactification, `o` be an orientation of `a` of relative dimension
`d` with twist `T = Λ_X(d)`, and `K` be perfect over `Λ_X`. If the projection formula holds for
`a` at `K` and the shifts `Λ_s[r]` of the constant complex of the point `s = Spec k`, then the
tensor–internal-hom adjoint of the derived Poincaré pairing

`β_K : RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ`

is an isomorphism `RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨` of the point category; that is, `β_K` is
perfect. Following the blueprint, it suffices to check this after applying `Hom(Λ_s[r], -)`
for all `r` (`AlgebraicGeometry.Etale.isIso_iff_bijective_comp_of_isSepClosed`, blueprint
`lem-sf-detection`), and there the adjoint of `β_K` is identified with the chain of the
tensor–hom exchange (`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isDetecting`).
-/
theorem isPerfectPairing_poincarePairing_of_isSepClosed
    (o : Orientation (ModuleCat.{u + 1} Λ) a d)
    (e : (L((a)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ≅ 𝟙_ _)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K)
    (hPF : ∀ r : ℤ, HasProjectionFormula (ModuleCat.{u + 1} Λ) a K
      (((_root_.DerivedCategory.singleFunctor _ 0).obj ((constantSheaf
        (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)))⟦r⟧)) :
    IsPerfectPairing (poincarePairing a o e K) := by
  set T := (_root_.DerivedCategory.singleFunctor _ 0).obj ((constantSheaf
    (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))
  refine isPerfectPairing_poincarePairing_of_isDetecting _ a o e hK (fun N ↦ ∃ r : ℤ, N = T⟦r⟧)
    (fun P Q u hu ↦ ?_) (fun N ⟨r, hr⟩ ↦ hr ▸ hPF r)
  refine (isIso_iff_bijective_comp_of_isSepClosed u).2 fun r ↦ ?_
  let E : (T⟦r - 2 * d⟧)⟦(2 * d : ℤ)⟧ ≅ T⟦r⟧ :=
    ((shiftFunctorAdd' _ (r - 2 * d) (2 * d) r (by omega)).app T).symm
  have hc : (fun g : T⟦r⟧ ⟶ P ↦ g ≫ u) =
      (fun g ↦ E.inv ≫ g) ∘ (fun g : (T⟦r - 2 * d⟧)⟦(2 * d : ℤ)⟧ ⟶ P ↦ g ≫ u) ∘
        (fun g ↦ E.hom ≫ g) := by
    funext g
    simp
  rw [hc]
  exact ((isIso_iff_coyoneda_map_bijective E.inv).1 inferInstance _).comp
    ((hu _ ⟨r - 2 * d, rfl⟩).comp ((isIso_iff_coyoneda_map_bijective E.hom).1 inferInstance _))

end Point

end Etale

end AlgebraicGeometry
