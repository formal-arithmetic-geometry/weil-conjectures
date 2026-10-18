/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Formal
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionHom
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality

/-!
# Finite exceptional adjoints and Verdier duality

For a finite coefficient ring `Λ` whose exponent is invertible on an algebraically closed field
`k`, and a morphism `f : X ⟶ Y` of separated schemes of finite type over `k`, the exceptional
inverse image of an object `L` of `Dctf(Y, Λ)` is computed by Verdier duality:

`Rf^! L ≅ 𝔻_X (Lf^* (𝔻_Y L))`

(blueprint `lem-coef-finite-exceptional`). Consequently `Rf^!` carries a constructible complex of
Tor amplitude in `[a, b]` to a constructible complex of Tor amplitude in
`[a - 2 dim X, b + 2 dim Y]`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_of_constructibleFiniteTor`:
  the duality formula.
- `AlgebraicGeometry.Etale.constructibleFiniteTor_and_torAmplitudeIn_rightDerivedUpperShriek`:
  the Tor amplitude bound.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
  [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY]
  (f : X ⟶ Y) [HasCompactification f] [HasCompactification (f ≫ aY)] [QuasiCompact (f ≫ aY)]

/-- Blueprint `lem-coef-finite-exceptional`: Finite exceptional adjoints and coefficient change,
the duality formula.

For a finite `Λ` whose exponent is invertible on an algebraically closed field `k`, a separated
finite-type `k`-scheme `Y` with structure morphism `a_Y`, and `f : X ⟶ Y` (with `a_X = f ≫ a_Y`),
every `L ∈ Dctf(Y, Λ)` satisfies `Rf^! L ≅ 𝔻_X (Lf^* (𝔻_Y L))`: by biduality
`L ≅ 𝔻_Y 𝔻_Y L` (`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual`), and duality
against pullback `𝔻_X (Lf^* M) ≅ Rf^! (𝔻_Y M)`
(`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_leftDerivedUpperStar`) at `M = 𝔻_Y L`. -/
theorem nonempty_iso_rightDerivedUpperShriek_of_constructibleFiniteTor
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L) :
    Nonempty ((R(f)^![ModuleCat.{u + 1} Λ]).obj L ≅
      (verdierDual (ModuleCat.{u + 1} Λ) (f ≫ aY)).obj
        (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj
          ((verdierDual (ModuleCat.{u + 1} Λ) aY).obj (op L))))) := by
  obtain ⟨β⟩ := nonempty_iso_verdierDual_verdierDual Λ aY hL
  obtain ⟨e⟩ := nonempty_iso_verdierDual_leftDerivedUpperStar Λ aY f
    ((verdierDual (ModuleCat.{u + 1} Λ) aY).obj (op L))
  exact ⟨(R(f)^![ModuleCat.{u + 1} Λ]).mapIso β ≪≫ e.symm⟩

/-- Blueprint `lem-coef-finite-exceptional`: Finite exceptional adjoints and coefficient change,
the Tor interval of the finite exceptional adjoint.

In the situation of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_of_constructibleFiniteTor`,
with `X` separated of finite type over `k` and `dim X ≤ d_X`, `dim Y ≤ d_Y`: if `L` is bounded
constructible of Tor amplitude in `[a, b]`, then `Rf^! L` lies in `Dctf(X, Λ)` with Tor amplitude
in `[a - 2 d_X, b + 2 d_Y]`. Indeed `𝔻_Y` sends `[a, b]` to `[-b - 2 d_Y, -a]`
(`AlgebraicGeometry.Etale.torAmplitudeIn_verdierDual`), `Lf^*` preserves Tor amplitude, and
`𝔻_X` then gives `[a - 2 d_X, b + 2 d_Y]`. -/
theorem constructibleFiniteTor_and_torAmplitudeIn_rightDerivedUpperShriek
    [IsSeparated (f ≫ aY)] [LocallyOfFiniteType (f ≫ aY)] (dX dY : ℕ)
    (hdX : topologicalKrullDim X ≤ (dX : WithBot ℕ∞))
    (hdY : topologicalKrullDim Y ≤ (dY : WithBot ℕ∞)) (a b : ℤ)
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : boundedConstructible (ModuleCat.{u + 1} Λ) Y L)
    (hLt : torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b L) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X ((R(f)^![ModuleCat.{u + 1} Λ]).obj L) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * (dX : ℤ)) (b + 2 * (dY : ℤ))
        ((R(f)^![ModuleCat.{u + 1} Λ]).obj L) := by
  have hctf : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L := ⟨hL, a, b, hLt⟩
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_of_constructibleFiniteTor Λ aY f hctf
  have h₁ := constructibleFiniteTor_verdierDual Λ aY hctf
  have h₁t := torAmplitudeIn_verdierDual Λ aY dY hdY a b hL hLt
  have h₂ := constructibleFiniteTor_leftDerivedUpperStar _ f h₁
  have h₂t := torAmplitudeIn_leftDerivedUpperStar _ f _ _ h₁t
  have h₃ := constructibleFiniteTor_verdierDual Λ (f ≫ aY) h₂
  have h₃t := torAmplitudeIn_verdierDual Λ (f ≫ aY) dX hdX _ _ h₂.1 h₂t
  refine ⟨(constructibleFiniteTor _ X).prop_of_iso e.symm h₃,
    (torAmplitudeIn _ X _ _).prop_of_iso e.symm ?_⟩
  convert h₃t using 2 <;> ring

section CoefficientChange

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B] {φ : A →+* B}
  (hφ : Function.Surjective φ) {a : A} (ha : RingHom.ker φ = Ideal.span {a})
  {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent A (Spec (.of k))] [HasInvertibleExponent B (Spec (.of k))]

include hφ ha in
/-- Blueprint `cor-coef-finite-verdier`: Finite reductions of Verdier duality.

For finite coefficient rings and a surjection `φ : A →+* B` with principal kernel, and for
`K ∈ Dctf(X, A)` on a separated finite-type `k`-scheme `X`, the Verdier dual commutes with the
coefficient change: `(𝔻_{X,A} K) ⊗ᴸ_A B ≅ 𝔻_{X,B}(K ⊗ᴸ_A B)`. (The comparison map of the
blueprint, its cocycle and its compatibility with evaluation are not formalised.) -/
theorem nonempty_iso_derivedExtendScalars_verdierDual {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [HasCompactification aX]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} A) X K) :
    Nonempty ((derivedExtendScalars hφ ha X).obj
        ((verdierDual (ModuleCat.{u + 1} A) aX).obj (op K)) ≅
      (verdierDual (ModuleCat.{u + 1} B) aX).obj (op ((derivedExtendScalars hφ ha X).obj K))) :=
  sorry

include hφ ha in
/-- The derived extension of scalars `- ⊗ᴸ_A B` commutes with the pullback `Lf^*` (the
"coefficient tensor commutes with ordinary pullback" of blueprint
`lem-coef-finite-exceptional`). Both are left adjoints, of `Rf_* ∘ Res` and `Res ∘ Rf_*`, which
agree. -/
theorem nonempty_iso_derivedExtendScalars_leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    Nonempty ((derivedExtendScalars hφ ha X).obj ((L((f)^*[ModuleCat.{u + 1} A])).obj K) ≅
      (L((f)^*[ModuleCat.{u + 1} B])).obj ((derivedExtendScalars hφ ha Y).obj K)) :=
  sorry

include hφ ha in
/-- Blueprint `lem-coef-finite-exceptional`: Finite exceptional adjoints and coefficient change,
the coefficient reduction.

For finite coefficient rings, a surjection `φ : A →+* B` with principal kernel (for instance
`A_m ⟶ A_n`, `m ≥ n`), and `L ∈ Dctf(Y, A)`:
`(Rf_A^! L) ⊗ᴸ_A B ≅ Rf_B^!(L ⊗ᴸ_A B)`.
As in the blueprint, apply the duality formula
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_of_constructibleFiniteTor` and
the coefficient change of the two Verdier duals
(`AlgebraicGeometry.Etale.nonempty_iso_derivedExtendScalars_verdierDual`,
`cor-coef-finite-verdier`),
the coefficient change commuting with ordinary pullback. (The cocycle and the compatibility with
the units and counits are not formalised: the comparison is only asserted to exist.) -/
theorem nonempty_iso_derivedExtendScalars_rightDerivedUpperShriek {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasCompactification aY] (f : X ⟶ Y) [HasCompactification f] [HasCompactification (f ≫ aY)]
    [QuasiCompact (f ≫ aY)] [IsSeparated (f ≫ aY)] [LocallyOfFiniteType (f ≫ aY)]
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (hL : constructibleFiniteTor (ModuleCat.{u + 1} A) Y L) :
    Nonempty ((derivedExtendScalars hφ ha X).obj ((R(f)^![ModuleCat.{u + 1} A]).obj L) ≅
      (R(f)^![ModuleCat.{u + 1} B]).obj ((derivedExtendScalars hφ ha Y).obj L)) := by
  let DA := verdierDual (ModuleCat.{u + 1} A) aY
  let DB := verdierDual (ModuleCat.{u + 1} B) aY
  let EY := derivedExtendScalars hφ ha Y
  have hD := constructibleFiniteTor_verdierDual A aY hL
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_of_constructibleFiniteTor A aY f hL
  obtain ⟨v₁⟩ := nonempty_iso_derivedExtendScalars_verdierDual hφ ha (f ≫ aY)
    (constructibleFiniteTor_leftDerivedUpperStar _ f hD)
  obtain ⟨p⟩ := nonempty_iso_derivedExtendScalars_leftDerivedUpperStar hφ ha f (DA.obj (op L))
  obtain ⟨v₂⟩ := nonempty_iso_derivedExtendScalars_verdierDual hφ ha aY hL
  obtain ⟨v₃⟩ := nonempty_iso_derivedExtendScalars_verdierDual hφ ha aY hD
  obtain ⟨β⟩ := nonempty_iso_verdierDual_verdierDual A aY hL
  obtain ⟨d⟩ := nonempty_iso_verdierDual_leftDerivedUpperStar B aY f (DB.obj (op (EY.obj L)))
  -- `𝔻_B 𝔻_B (L ⊗ B) ≅ 𝔻_B ((𝔻_A L) ⊗ B) ≅ (𝔻_A 𝔻_A L) ⊗ B ≅ L ⊗ B`
  let b : DB.obj (op (DB.obj (op (EY.obj L)))) ≅ EY.obj L :=
    DB.mapIso v₂.op ≪≫ v₃.symm ≪≫ EY.mapIso β.symm
  exact ⟨(derivedExtendScalars hφ ha X).mapIso e₁ ≪≫ v₁ ≪≫
    ((verdierDual (ModuleCat.{u + 1} B) (f ≫ aY)).mapIso
      (p ≪≫ (L((f)^*[ModuleCat.{u + 1} B])).mapIso v₂).op).symm ≪≫ d ≪≫
    (R(f)^![ModuleCat.{u + 1} B]).mapIso b⟩

end CoefficientChange

end Etale

end AlgebraicGeometry
