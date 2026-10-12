/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual

/-!
# Verdier duality on the geometric generic fibre

Let `B` be an integral scheme with function field `K(B)` and let `η̄ : Spec \overline{K(B)} ⟶ B`
be its geometric generic point (`AlgebraicGeometry.Scheme.geometricGenericPoint`). For a
`B`-scheme `X` write `X_η̄ = X ×_B η̄` for the geometric generic fibre and `g_X : X_η̄ ⟶ X` for the
projection. This file states the comparisons between the operations on `X` and on `X_η̄` that
drive the dimension induction in the proof of Verdier biduality
(`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app`).

## Main statements

- `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_geometricGenericPoint` and its
  companions for `Ri^!` and `RHom`
  (`lem-weil-geometric-generic-exchange`): over a smooth integral curve `B`, geometric generic
  pullback commutes with `Rh_*`, with `Ri^!` for closed immersions `i`, and with `RHom(K, -)`
  for `K ∈ Dctf`.
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_dualizingComplex_geometricGenericPoint`
  and its companion for the double-dual morphism
  (`lem-weil-geometric-generic-duality`): for `p : X ⟶ 𝔸¹_k`, `g^* ω_X ≅ ω_{X_η̄}(1)[2]` on every
  affine open of `X`, and `g^* δ_K` is an isomorphism if and only if `δ_{g^* K}` is.

## Implementation notes

The affine line is `Spec k[t]`. The exchange for `Ri^!` is stated as the existence of an
isomorphism, as is the exchange `Ri^! 𝔻_T ≅ 𝔻_Z i^*` of `lem-weil-closed-costalk-duality`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_verdierDual`); the other two
exchanges are stated for the canonical comparison maps.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

/-- The geometric generic point `η̄ : Spec \overline{K(B)} ⟶ B` of an integral scheme `B`: the
spectrum of an algebraic closure of the function field `K(B)`, mapping to the generic point. -/
noncomputable def Scheme.geometricGenericPoint (B : Scheme.{u}) [IsIntegral B] :
    Spec (.of (AlgebraicClosure B.functionField)) ⟶ B :=
  Spec.map (CommRingCat.ofHom (algebraMap B.functionField (AlgebraicClosure B.functionField))) ≫
    B.fromSpecStalk (genericPoint B)

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]

section Exchange

variable {B : Scheme.{u}} [IsIntegral B] (b : B ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 b]

/-- The base change `h_η̄ : T_η̄ ⟶ X_η̄` of a `B`-morphism `h : T ⟶ X` to the geometric generic
fibres. -/
noncomputable def geometricGenericFibreMap {X T : Scheme.{u}} {πX : X ⟶ B} {πT : T ⟶ B}
    (h : T ⟶ X) (hh : h ≫ πX = πT) :
    pullback πT B.geometricGenericPoint ⟶ pullback πX B.geometricGenericPoint :=
  pullback.map _ _ _ _ h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)

lemma geometricGenericFibreMap_commSq {X T : Scheme.{u}} {πX : X ⟶ B} {πT : T ⟶ B}
    (h : T ⟶ X) (hh : h ≫ πX = πT) :
    CommSq (pullback.fst πT B.geometricGenericPoint) (geometricGenericFibreMap h hh) h
      (pullback.fst πX B.geometricGenericPoint) :=
  ⟨by simp [geometricGenericFibreMap]⟩

instance isClosedImmersion_geometricGenericFibreMap {X T : Scheme.{u}} {πX : X ⟶ B}
    {πT : T ⟶ B} (h : T ⟶ X) [IsClosedImmersion h] (hh : h ≫ πX = πT) :
    IsClosedImmersion (geometricGenericFibreMap h hh) :=
  MorphismProperty.pullbackMap (P := @IsClosedImmersion) (i₂ := 𝟙 _) inferInstance
    inferInstance hh.symm (Category.id_comp _).symm

include b

/-- Blueprint `lem-weil-geometric-generic-exchange`: Restriction to the geometric generic fibre.

Let `B` be a smooth integral curve over `k`, `η̄` its geometric generic point and `g` the
geometric generic pullback on `B`-schemes of finite type. For a separated finite-type
`B`-morphism `h : T ⟶ X` and `L ∈ Dᵇc(T, Λ)`, the derived base change map
`g_X^* Rh_* L ⟶ Rh_{η̄ *} g_T^* L` is an isomorphism. -/
theorem isIso_derivedBaseChangeMap_geometricGenericPoint {X T : Scheme.{u}} (πX : X ⟶ B)
    (πT : T ⟶ B) [LocallyOfFiniteType πX] [QuasiCompact πX] [LocallyOfFiniteType πT]
    [QuasiCompact πT] (h : T ⟶ X) (hh : h ≫ πX = πT) [IsSeparated h] [LocallyOfFiniteType h]
    [QuasiCompact h]
    {L : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : boundedConstructible (ModuleCat.{u + 1} Λ) T L) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (geometricGenericFibreMap_commSq h hh)).app L) :=
  sorry

/-- Blueprint `lem-weil-geometric-generic-exchange`: Restriction to the geometric generic fibre.

Let `B` be a smooth integral curve over `k`, `η̄` its geometric generic point and `g` the
geometric generic pullback on `B`-schemes of finite type. For a closed immersion `i : Z ⟶ X`
of `B`-schemes and `M ∈ Dᵇc(X, Λ)`, the exceptional restriction commutes with `g`:
`g_Z^* Ri^! M ≅ Ri_{η̄}^! g_X^* M`. -/
theorem nonempty_iso_leftDerivedUpperStar_rightDerivedUpperShriek_geometricGenericPoint
    {X Z : Scheme.{u}} (πX : X ⟶ B) [LocallyOfFiniteType πX] [QuasiCompact πX] (i : Z ⟶ X)
    [IsClosedImmersion i]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M) :
    Nonempty ((L((pullback.fst (i ≫ πX) B.geometricGenericPoint)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(i)^![ModuleCat.{u + 1} Λ]).obj M) ≅
      (R(geometricGenericFibreMap i rfl)^![ModuleCat.{u + 1} Λ]).obj
        ((L((pullback.fst πX B.geometricGenericPoint)^*[ModuleCat.{u + 1} Λ])).obj M)) :=
  sorry

/-- Blueprint `lem-weil-geometric-generic-exchange`: Restriction to the geometric generic fibre.

Let `B` be a smooth integral curve over `k`, `η̄` its geometric generic point and
`g : X_η̄ ⟶ X` the geometric generic pullback of a `B`-scheme `X` of finite type. For
`K ∈ Dctf(X, Λ)` and `M ∈ Dᵇc(X, Λ)`, the comparison map
`g^* RHom(K, M) ⟶ RHom(g^* K, g^* M)` of the monoidal functor `g^*` is an isomorphism. -/
theorem isIso_ihomComparison_geometricGenericPoint {X : Scheme.{u}} (πX : X ⟶ B)
    [LocallyOfFiniteType πX] [QuasiCompact πX]
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M) :
    letI := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ)
      (pullback.fst πX B.geometricGenericPoint)
    IsIso ((ihomComparison L((pullback.fst πX B.geometricGenericPoint)^*[ModuleCat.{u + 1} Λ])
      K).natTrans.app M) :=
  sorry

end Exchange

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
`a_η̄ : X_η̄ ⟶ η̄`. On every affine open `U` of `X`, `g^* ω_U ≅ ω_{U_η̄}(1)[2]`. -/
theorem nonempty_iso_leftDerivedUpperStar_dualizingComplex_geometricGenericPoint
    [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ]
    (hp : p ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = a)
    (U : X.affineOpens) [IsSeparated (U.1.ι ≫ a)] [LocallyOfFiniteType (U.1.ι ≫ a)]
    [QuasiCompact (U.1.ι ≫ a)] [IsSeparated (U.1.ι ≫ p)] [LocallyOfFiniteType (U.1.ι ≫ p)]
    [QuasiCompact (U.1.ι ≫ p)] [HasCompactification (U.1.ι ≫ a)]
    [HasCompactification (pullback.snd (U.1.ι ≫ p) (affineLineGeometricGenericPoint k))] :
    Nonempty ((L((pullback.fst (U.1.ι ≫ p)
        (affineLineGeometricGenericPoint k))^*[ModuleCat.{u + 1} Λ])).obj
          (dualizingComplex (ModuleCat.{u + 1} Λ) (U.1.ι ≫ a)) ≅
      (twistShift Λ _ 1).obj (dualizingComplex (ModuleCat.{u + 1} Λ)
        (pullback.snd (U.1.ι ≫ p) (affineLineGeometricGenericPoint k)))) :=
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
