/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GeometricGenericHom

/-!
# The double dual on a geometric generic fibre

For `p : X ⟶ 𝔸¹_k` with geometric generic fibre `g : X_η̄ ⟶ X`, `g^* ω_X ≅ ω_{X_η̄}(1)[2]`
Zariski locally on `X`, and `g^* δ_K` is an isomorphism if and only if `δ_{g^* K}` is
(`lem-weil-geometric-generic-duality`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

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
-- unifying the categories of `δ_{g^* K}` and of `g^* K` unfolds the derived category instances
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
            K)) :=
  sorry

end Duality

end Etale

end AlgebraicGeometry
