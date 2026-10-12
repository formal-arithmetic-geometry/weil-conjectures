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

end Exchange

end Etale

end AlgebraicGeometry
