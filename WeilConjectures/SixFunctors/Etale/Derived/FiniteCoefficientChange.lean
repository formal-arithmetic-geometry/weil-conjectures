/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsQuotientDerived

/-!
# Change of finite coefficients for the six operations and Verdier duality

Let `Λ` be a finite commutative ring whose exponent is invertible on the base field `k`, let
`J` be an ideal of `Λ` and `B = Λ ⧸ J`; the intended case is `Λ = A_{E,m} = 𝒪_E ⧸ ϖᵐ` and
`B = A_{E,n}` for `n ≤ m`. The change of coefficients
`K ↦ K_B = K ⊗ᴸ_Λ B : D(X_ét, Λ) ⥤ D(X_ét, B)` is the derived extension of scalars
(`AlgebraicGeometry.Etale.coefficientChange`). This file records how it interacts with the
operations on the finite-Tor constructible categories `Dctf`:

- `AlgebraicGeometry.Etale.nonempty_iso_coefficientChange_rightDerivedLowerStar`
  (`lem-coef-finite-direct-image`): `(Rf_* K)_B ≅ Rf_*(K_B)`;
- `AlgebraicGeometry.Etale.nonempty_iso_coefficientChange_rightDerivedUpperShriek`
  (`lem-coef-finite-closed-shriek`): `(Ri^! M)_B ≅ Ri^!(M_B)` for a closed immersion `i`;
- `AlgebraicGeometry.Etale.nonempty_iso_coefficientChange_dualizingComplex`
  (`lem-coef-finite-dualizing`): `(ω_{X,Λ})_B ≅ ω_{X,B}`;
- `AlgebraicGeometry.Etale.nonempty_iso_coefficientChange_derivedHom`
  (`thm-coef-finite-hom`): `RHom_Λ(K, M)_B ≅ RHom_B(K_B, M_B)`;
- `AlgebraicGeometry.Etale.nonempty_iso_coefficientChange_verdierDual`
  (`cor-coef-finite-verdier`): `(𝔻_{X,Λ} K)_B ≅ 𝔻_{X,B}(K_B)`, with the Tor bound;
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_verdierDual_comp` and
  `AlgebraicGeometry.Etale.nonempty_iso_coefficientChange_rightDerivedUpperShriek_of_isSeparated`
  (`lem-coef-finite-exceptional`): `Rf^! L ≅ 𝔻_X f^* 𝔻_Y L` and `(Rf^! L)_B ≅ Rf^!(L_B)`.

## Implementation notes

As elsewhere in this directory (`AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_verdierDual`),
the canonical comparison maps of the blueprint are not constructed: the comparisons are stated
as the existence of isomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

/-- An exponent of `Λ` invertible on `X` is an exponent of any quotient of `Λ`. -/
instance HasInvertibleExponent.quotient {Λ : Type*} [CommRing Λ] (J : Ideal Λ) (X : Scheme.{u})
    [HasInvertibleExponent Λ X] : HasInvertibleExponent (Λ ⧸ J) X := by
  obtain ⟨n, hn, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := X)
  exact ⟨n, hn, by rw [← map_natCast (Ideal.Quotient.mk J), hΛ, map_zero], hu⟩

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {Λ : Type (u + 1)} [CommRing Λ] (J : Ideal Λ)

/-- The change of coefficients `K ↦ K ⊗ᴸ_Λ (Λ ⧸ J) : D(X_ét, Λ) ⥤ D(X_ét, Λ ⧸ J)`, the derived
extension of scalars along `Λ ⟶ Λ ⧸ J`. It is left adjoint to restriction of scalars
(`AlgebraicGeometry.Etale.derivedExtendScalarsAdjunction`), and restricting the scalars of
`K_B` back to `Λ` gives the reduction `K ⊗ᴸ (Λ ⧸ J)_X`
(`AlgebraicGeometry.Etale.nonempty_iso_restrictScalars_leftDerived_obj`). -/
noncomputable abbrev coefficientChange (X : Scheme.{u}) : 𝐃(X, Λ) ⥤ 𝐃(X, Λ ⧸ J) :=
  (ProEtale.etaleSheafExtendScalars (Ideal.Quotient.mk J) X).leftDerivedFunctor

variable [Finite Λ] {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]

/-- A quotient of a finite ring is finite. -/
instance finite_quotient : Finite (Λ ⧸ J) :=
  Finite.of_surjective _ Ideal.Quotient.mk_surjective

/-- Derived extension of scalars along `Λ ⟶ Λ ⧸ J` preserves Tor amplitude in `[p, q]`: the Tor
amplitude of `K ⊗ᴸ_Λ B` over `B` is computed by `(K ⊗ᴸ_Λ B) ⊗ᴸ_B N = K ⊗ᴸ_Λ N` for `B`-modules
`N`. This is the preservation of the Tor interval by scalar extension used in the blueprint
proof of `cor-coef-finite-verdier`. -/
theorem torAmplitudeIn_coefficientChange {X : Scheme.{u}} (p q : ℤ) {K : 𝐃(X, Λ)}
    (hK : torAmplitudeIn (ModuleCat.{u + 1} Λ) X p q K) :
    torAmplitudeIn (ModuleCat.{u + 1} (Λ ⧸ J)) X p q ((coefficientChange J X).obj K) :=
  sorry

/-- Derived extension of scalars along `Λ ⟶ Λ ⧸ J` carries `Dctf(X, Λ)` to bounded
constructible complexes. -/
theorem boundedConstructible_coefficientChange {X : Scheme.{u}} {K : 𝐃(X, Λ)}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    boundedConstructible (ModuleCat.{u + 1} (Λ ⧸ J)) X ((coefficientChange J X).obj K) :=
  sorry

/-- Derived extension of scalars along `Λ ⟶ Λ ⧸ J` preserves `Dctf`. -/
theorem constructibleFiniteTor_coefficientChange {X : Scheme.{u}} {K : 𝐃(X, Λ)}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    constructibleFiniteTor (ModuleCat.{u + 1} (Λ ⧸ J)) X ((coefficientChange J X).obj K) := by
  obtain ⟨p, q, hpq⟩ := hK.2
  exact ⟨boundedConstructible_coefficientChange J hK, p, q,
    torAmplitudeIn_coefficientChange J p q hpq⟩

/-- Derived extension of scalars commutes with derived pullback: `(f^* K)_B ≅ f^*(K_B)`, both
being left adjoint to `Rf_* ∘ Res ≅ Res ∘ Rf_*`. -/
theorem nonempty_iso_coefficientChange_leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : 𝐃(Y, Λ)) :
    Nonempty ((coefficientChange J X).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (L((f)^*[ModuleCat.{u + 1} (Λ ⧸ J)])).obj ((coefficientChange J Y).obj K)) :=
  sorry

/-- The dualizing complex `ω_X = Ra^! Λ` lies in `Dctf(X, Λ)`: it is `𝔻_X Λ_X`, and the Verdier
dual preserves `Dctf` (`lem-weil-verdier-preservation-strata`, applied to `Λ_X`). -/
theorem constructibleFiniteTor_dualizingComplex [IsAlgClosed k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [HasCompactification a] :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (dualizingComplex (ModuleCat.{u + 1} Λ) a) :=
  sorry

/-- Blueprint `lem-coef-finite-direct-image`: Finite coefficient change for ordinary direct
image.

Let `f : T ⟶ X` be a separated morphism of finite type between schemes of finite type over a
separably closed field `k`, and `K ∈ Dctf(T, Λ)`. Then `(Rf_* K) ⊗ᴸ_Λ B ≅ Rf_*(K ⊗ᴸ_Λ B)` for
`B = Λ ⧸ J`. -/
theorem nonempty_iso_coefficientChange_rightDerivedLowerStar [IsSepClosed k]
    {T X : Scheme.{u}} (aT : T ⟶ Spec (.of k)) (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aT]
    [QuasiCompact aT] [LocallyOfFiniteType aX] [QuasiCompact aX] (f : T ⟶ X) (hf : f ≫ aX = aT)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] {K : 𝐃(T, Λ)}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) T K) :
    Nonempty ((coefficientChange J X).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (R((f)_*[ModuleCat.{u + 1} (Λ ⧸ J)])).obj ((coefficientChange J T).obj K)) :=
  sorry

/-- Blueprint `lem-coef-finite-dualizing`: Finite coefficient change for the dualizing object.

For `X` separated of finite type over an algebraically closed field `k`, with structure
morphism `a`, the dualizing complexes `ω_{X,Λ} = Ra^! Λ` and `ω_{X,B} = Ra^! B` satisfy
`ω_{X,Λ} ⊗ᴸ_Λ B ≅ ω_{X,B}` for `B = Λ ⧸ J`. -/
theorem nonempty_iso_coefficientChange_dualizingComplex [IsAlgClosed k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [HasCompactification a] :
    Nonempty ((coefficientChange J X).obj (dualizingComplex (ModuleCat.{u + 1} Λ) a) ≅
      dualizingComplex (ModuleCat.{u + 1} (Λ ⧸ J)) a) :=
  sorry

/-- Blueprint `thm-coef-finite-hom`: Finite coefficient change for internal Hom.

For `X` separated of finite type over an algebraically closed field `k` and
`K, M ∈ Dctf(X, Λ)`, `RHom_Λ(K, M) ⊗ᴸ_Λ B ≅ RHom_B(K ⊗ᴸ_Λ B, M ⊗ᴸ_Λ B)` for `B = Λ ⧸ J`. -/
theorem nonempty_iso_coefficientChange_derivedHom [IsAlgClosed k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    {K M : 𝐃(X, Λ)} (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M) :
    Nonempty ((coefficientChange J X).obj
        (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj M) ≅
      ((derivedHom (ModuleCat.{u + 1} (Λ ⧸ J)) X).obj (op ((coefficientChange J X).obj K))).obj
        ((coefficientChange J X).obj M)) :=
  sorry

/-- Blueprint `cor-coef-finite-verdier`: Finite coefficient change for Verdier duality.

For `X` separated of finite type over an algebraically closed field `k` and `K ∈ Dctf(X, Λ)`,
`(𝔻_{X,Λ} K) ⊗ᴸ_Λ B ≅ 𝔻_{X,B}(K ⊗ᴸ_Λ B)` for `B = Λ ⧸ J`; if `dim X ≤ d` and `K` has Tor
amplitude in `[a, b]`, so does `K ⊗ᴸ_Λ B` over `B`, and both sides have Tor amplitude in
`[-b - 2d, -a]` over `B`. -/
theorem nonempty_iso_coefficientChange_verdierDual [IsAlgClosed k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [HasCompactification a] {K : 𝐃(X, Λ)}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    Nonempty ((coefficientChange J X).obj ((verdierDual (ModuleCat.{u + 1} Λ) a).obj (op K)) ≅
      (verdierDual (ModuleCat.{u + 1} (Λ ⧸ J)) a).obj (op ((coefficientChange J X).obj K))) ∧
    ∀ (d : ℕ), topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ (p q : ℤ),
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X p q K →
        torAmplitudeIn (ModuleCat.{u + 1} (Λ ⧸ J)) X p q ((coefficientChange J X).obj K) ∧
        torAmplitudeIn (ModuleCat.{u + 1} (Λ ⧸ J)) X (-q - 2 * (d : ℤ)) (-p)
          ((verdierDual (ModuleCat.{u + 1} (Λ ⧸ J)) a).obj
            (op ((coefficientChange J X).obj K))) := by
  refine ⟨?_, fun d hd p q hpq ↦ ?_⟩
  · sorry
  · have h := torAmplitudeIn_coefficientChange J p q hpq
    exact ⟨h, torAmplitudeIn_verdierDual (Λ ⧸ J) a d hd p q
      (boundedConstructible_coefficientChange J hK) h⟩

/-- Blueprint `lem-coef-finite-exceptional`: Finite exceptional inverse image and coefficient
change, the description through Verdier duality.

For a separated morphism of finite type `f : X ⟶ Y` of schemes separated of finite type over an
algebraically closed field `k` and `L ∈ Dctf(Y, Λ)`, `Rf^! L ≅ 𝔻_X (f^* (𝔻_Y L))`. -/
theorem nonempty_iso_rightDerivedUpperShriek_verdierDual_comp [IsAlgClosed k]
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [IsSeparated aX]
    [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX] [IsSeparated aY]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY] (f : X ⟶ Y)
    (hf : f ≫ aY = aX) [HasCompactification f] {L : 𝐃(Y, Λ)}
    (hL : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L) :
    Nonempty ((R(f)^![ModuleCat.{u + 1} Λ]).obj L ≅
      (verdierDual (ModuleCat.{u + 1} Λ) aX).obj (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj
        ((verdierDual (ModuleCat.{u + 1} Λ) aY).obj (op L))))) :=
  sorry

/-- Blueprint `lem-coef-finite-exceptional`: Finite exceptional inverse image and coefficient
change, the reduction.

For a separated morphism of finite type `f : X ⟶ Y` of schemes separated of finite type over an
algebraically closed field `k` and `L ∈ Dctf(Y, Λ)`, `(Rf^! L) ⊗ᴸ_Λ B ≅ Rf^!(L ⊗ᴸ_Λ B)` for
`B = Λ ⧸ J`. -/
theorem nonempty_iso_coefficientChange_rightDerivedUpperShriek_of_isSeparated [IsAlgClosed k]
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [IsSeparated aX]
    [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX] [IsSeparated aY]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY] (f : X ⟶ Y)
    (hf : f ≫ aY = aX) [HasCompactification f] {L : 𝐃(Y, Λ)}
    (hL : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L) :
    Nonempty ((coefficientChange J X).obj ((R(f)^![ModuleCat.{u + 1} Λ]).obj L) ≅
      (R(f)^![ModuleCat.{u + 1} (Λ ⧸ J)]).obj ((coefficientChange J Y).obj L)) := by
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_verdierDual_comp (k := k) aX aY f hf hL
  have hD : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      ((L((f)^*[ModuleCat.{u + 1} Λ])).obj ((verdierDual (ModuleCat.{u + 1} Λ) aY).obj (op L))) :=
    constructibleFiniteTor_leftDerivedUpperStar _ f (constructibleFiniteTor_verdierDual Λ aY hL)
  obtain ⟨e₂⟩ := (nonempty_iso_coefficientChange_verdierDual J aX hD).1
  obtain ⟨e₃⟩ := nonempty_iso_coefficientChange_leftDerivedUpperStar J f
    ((verdierDual (ModuleCat.{u + 1} Λ) aY).obj (op L))
  obtain ⟨e₄⟩ := (nonempty_iso_coefficientChange_verdierDual J aY hL).1
  obtain ⟨e₅⟩ := nonempty_iso_rightDerivedUpperShriek_verdierDual_comp (Λ := Λ ⧸ J) (k := k)
    aX aY f hf (constructibleFiniteTor_coefficientChange J hL)
  exact ⟨(coefficientChange J X).mapIso e₁ ≪≫ e₂ ≪≫
    (verdierDual (ModuleCat.{u + 1} (Λ ⧸ J)) aX).mapIso
      (e₃ ≪≫ (L((f)^*[ModuleCat.{u + 1} (Λ ⧸ J)])).mapIso e₄).symm.op ≪≫ e₅.symm⟩

/-- Blueprint `lem-coef-finite-closed-shriek`: Finite coefficient change for closed exceptional
inverse image.

For a closed immersion `i : Z ⟶ X` of schemes of finite type over an algebraically closed
field `k` and `M ∈ Dctf(X, Λ)`, `(Ri^! M) ⊗ᴸ_Λ B ≅ Ri^!(M ⊗ᴸ_Λ B)` for `B = Λ ⧸ J`. -/
theorem nonempty_iso_coefficientChange_rightDerivedUpperShriek [IsAlgClosed k]
    {Z X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
    [QuasiCompact aX] (i : Z ⟶ X) [IsClosedImmersion i] [HasCompactification i] {M : 𝐃(X, Λ)}
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M) :
    Nonempty ((coefficientChange J Z).obj ((R(i)^![ModuleCat.{u + 1} Λ]).obj M) ≅
      (R(i)^![ModuleCat.{u + 1} (Λ ⧸ J)]).obj ((coefficientChange J X).obj M)) := by
  have : HasCompactification aX := inferInstance
  have := HasCompactification.of_isClosedImmersion i aX
  exact nonempty_iso_coefficientChange_rightDerivedUpperShriek_of_isSeparated (k := k) J
    (i ≫ aX) aX i rfl hM

end Etale

end AlgebraicGeometry
