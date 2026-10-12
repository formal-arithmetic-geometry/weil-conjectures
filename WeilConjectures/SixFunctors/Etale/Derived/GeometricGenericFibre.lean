/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.FunctionFieldLimit
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedPlus
public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Limit
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.LimitBaseChange
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality

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

The exchange for `Rh_*` is proved on the bounded below derived categories
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_ι_iff`), by pasting two base changes:
along the generic fibre `X_K ⟶ X`, a limit of the open immersions of the nonempty affine opens of
`B` (`AlgebraicGeometry.Etale.isIso_baseChange_app_of_isLimit_of_smooth`, blueprint
`lem-kun-0f09`), and along the field extension `\overline{K(B)} / K(B)`
(`AlgebraicGeometry.Etale.isIso_baseChange_app_of_field`, blueprint `lem-kun-0f1c`).
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

namespace Scheme

variable (B : Scheme.{u}) [IsIntegral B]

/-- The nonempty affine opens `Spec Γ(B, U) ⟶ B` of an integral scheme `B`, as a diagram of
schemes over `B`. -/
noncomputable def affineOpensOverDiagram : B.NonemptyAffineOpens ⥤ Over B :=
  B.affineOpensDiagram.toOver B (fun U ↦ B.affineOpensDiagramι.app U)
    (fun φ ↦ by simpa using B.affineOpensDiagramι.naturality φ)

/-- The generic point `Spec k(B) ⟶ B` as a cone over the nonempty affine opens of `B`, in
schemes over `B`. -/
noncomputable def functionFieldOverCone : Cone B.affineOpensOverDiagram where
  pt := Over.mk B.fromSpecFunctionField
  π :=
    { app U := Over.homMk (B.functionFieldCone.π.app U)
        (fromSpecFunctionField_eq_functionFieldCone_comp B U).symm
      naturality U V φ := by
        ext1
        simpa [affineOpensOverDiagram] using (B.functionFieldCone.w φ).symm }

/-- The generic point `Spec k(B)` is the limit of the nonempty affine opens of `B`, as schemes
over `B`. -/
noncomputable def isLimitFunctionFieldOverCone :
    IsLimit ((Over.forget B).mapCone B.functionFieldOverCone) :=
  B.isLimitFunctionFieldCone

end Scheme

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
      (geometricGenericFibreMap_commSq h hh)).app L) := by
  subst hh
  have : Smooth b := SmoothOfRelativeDimension.smooth 1 b
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (πX ≫ b)
  have hopen (U : B.NonemptyAffineOpens) :
      IsOpenImmersion ((B.affineOpensOverDiagram.obj U).hom ≫ 𝟙 B) := by
    rw [Category.comp_id]
    exact inferInstanceAs (IsOpenImmersion (B.affineOpensDiagramι.app U))
  have hU (U : B.NonemptyAffineOpens) : IsAffine (B.affineOpensOverDiagram.obj U).left :=
    inferInstanceAs (IsAffine (Spec _))
  have htors (S : Scheme.{u}) (s : S ⟶ Spec (.of k)) {T' : Scheme.{u}}
      (F : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      Scheme.IsTorsionSheafOfInvertibleOrder S F := by
    have := HasInvertibleExponent.of_hom (Λ := Λ) s
    obtain ⟨n, hn, hnΛ, hnS⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := S)
    exact Scheme.IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero Λ n hn.ne' hnΛ hnS F
  let L₀ : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    ⟨L, hL.1.1⟩
  refine (isIso_derivedBaseChangeMap_app_ι_iff (ModuleCat.{u + 1} Λ) _ L₀).2 ?_
  -- the generic fibre `X_K = X ×_B Spec k(B)` as a limit of the `X ×_B U`
  set η := B.fromSpecFunctionField
  let a : Spec (.of (AlgebraicClosure B.functionField)) ⟶ Spec B.functionField :=
    Spec.map (CommRingCat.ofHom (algebraMap B.functionField (AlgebraicClosure B.functionField)))
  have hη : B.geometricGenericPoint = a ≫ η := rfl
  let sqX : IsPullback πX (𝟙 X) (𝟙 B) πX := IsPullback.of_id_snd
  let c := (Etale.stageFunctor sqX).mapCone B.functionFieldOverCone
  have hc := Etale.isLimitStageFunctorMapCone sqX B.functionFieldOverCone
    B.isLimitFunctionFieldOverCone
  have hstage (U : Over B) : ((Etale.stageFunctor sqX).obj U).hom =
      pullback.snd (U.hom ≫ 𝟙 B) πX :=
    (Category.comp_id _).symm.trans (sqX.lift_snd _ _ _)
  have hsm (U : B.NonemptyAffineOpens) :
      Smooth ((B.affineOpensOverDiagram ⋙ Etale.stageFunctor sqX).obj U).hom := by
    rw [Functor.comp_obj, hstage]
    infer_instance
  have hqc (U : B.NonemptyAffineOpens) :
      QuasiCompact ((B.affineOpensOverDiagram ⋙ Etale.stageFunctor sqX).obj U).hom := by
    rw [Functor.comp_obj, hstage]
    infer_instance
  have hqs (U : B.NonemptyAffineOpens) :
      QuasiSeparated ((B.affineOpensOverDiagram ⋙ Etale.stageFunctor sqX).obj U).hom := by
    rw [Functor.comp_obj, hstage]
    infer_instance
  have haff {U V : B.NonemptyAffineOpens} (φ : U ⟶ V) :
      IsAffineHom ((B.affineOpensOverDiagram ⋙ Etale.stageFunctor sqX).map φ).left := by
    rw [Functor.comp_map]
    infer_instance
  set p₂ := c.pt.hom
  have hp₂ : p₂ = pullback.snd (η ≫ 𝟙 B) πX := hstage _
  -- the base change of `h` to `X_K`
  let sq₂ := IsPullback.of_hasPullback h p₂
  -- the base change from `X_K` to the geometric generic fibre
  let p₁ : pullback πX B.geometricGenericPoint ⟶ pullback (η ≫ 𝟙 B) πX :=
    pullback.lift (pullback.snd πX B.geometricGenericPoint ≫ a)
      (pullback.fst πX B.geometricGenericPoint) (by simp [hη, pullback.condition])
  have hp : p₁ ≫ p₂ = pullback.fst πX B.geometricGenericPoint := by
    simp [hp₂, p₁]
  let e₁ : pullback (h ≫ πX) B.geometricGenericPoint ⟶ pullback h p₂ :=
    pullback.lift (pullback.fst (h ≫ πX) B.geometricGenericPoint)
      (geometricGenericFibreMap h rfl ≫ p₁)
      (by rw [Category.assoc, hp, (geometricGenericFibreMap_commSq h rfl).w])
  have he : e₁ ≫ pullback.fst h p₂ = pullback.fst (h ≫ πX) B.geometricGenericPoint :=
    pullback.lift_fst _ _ _
  have houter : IsPullback (pullback.fst (h ≫ πX) B.geometricGenericPoint)
      (geometricGenericFibreMap h rfl) h (pullback.fst πX B.geometricGenericPoint) :=
    IsPullback.of_bot (by simpa [geometricGenericFibreMap] using
        IsPullback.of_hasPullback (h ≫ πX) B.geometricGenericPoint)
      (geometricGenericFibreMap_commSq h rfl).w
      (IsPullback.of_hasPullback πX B.geometricGenericPoint)
  have sq₁ : IsPullback e₁ (geometricGenericFibreMap h rfl) (pullback.snd h p₂) p₁ :=
    IsPullback.of_right (by rwa [he, hp]) (by simp [e₁]) sq₂
  have hS : IsPullback p₁ (pullback.snd πX B.geometricGenericPoint)
      (pullback.fst (η ≫ 𝟙 B) πX) a := by
    refine IsPullback.of_right (h₁₂ := pullback.snd (η ≫ 𝟙 B) πX) (v₁₃ := πX) (h₂₂ := η) ?_
      (by simp [p₁]) ?_
    · have hp' : p₁ ≫ pullback.snd (η ≫ 𝟙 B) πX = pullback.fst πX B.geometricGenericPoint := by
        simp [p₁]
      rw [hp', ← hη]
      exact IsPullback.of_hasPullback πX B.geometricGenericPoint
    · simpa using (IsPullback.of_hasPullback (η ≫ 𝟙 B) πX).flip
  rw [Etale.baseChange_app_paste_horiz_of_eq Λ sq₂.toCommSq sq₁.toCommSq
    (geometricGenericFibreMap_commSq h rfl) he hp L₀]
  have : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq₂.toCommSq).app L₀) :=
    Etale.isIso_baseChange_app_of_isLimit_of_smooth Λ h _ _ hc sq₂ L₀
      fun _ ↦ htors X (πX ≫ b) _
  have : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq₁.toCommSq).app
      (D+((pullback.fst h p₂)^*[ModuleCat.{u + 1} Λ]).obj L₀)) :=
    Etale.isIso_baseChange_app_of_field Λ (pullback.fst (η ≫ 𝟙 B) πX) (pullback.snd h p₂) p₁
      (pullback.snd πX B.geometricGenericPoint) hS e₁ (geometricGenericFibreMap h rfl) sq₁ _
      fun _ ↦ htors _ (η ≫ b) _
  infer_instance

end Exchange

end Etale

end AlgebraicGeometry
