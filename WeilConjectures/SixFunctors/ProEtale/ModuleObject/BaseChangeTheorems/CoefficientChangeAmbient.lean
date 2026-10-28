/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeIntegralRational
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite
public import WeilConjectures.Tactic.ExactModProofs

/-!
# The base change map and the coefficient changes `𝒪_E ⟶ E ⟶ ℚ̄_ℓ` on the ambient categories

For a commutative square of schemes
```
X' --g'--> X
|p'        |p
v          v
Y' --g---> Y
```
the base change map `Lg^* Rp_* ⟶ Rp'_* Lg'^*` (`ProEtale.CondensedRing.baseChangeMap`) on the
ambient derived categories of module objects is compatible with flat changes of coefficients
whose (Push) comparisons are invertible
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_derivedExtendScalars`). For `p` and `p'`
quasi-compact and quasi-separated, this applies to the coefficient changes `𝒪_E ⟶ E ⟶ ℚ̄_ℓ` at
bounded below complexes: if the integral base change map is invertible at a bounded below
`𝒪_E`-complex `R₀`, the `ℚ̄_ℓ`-base change map is invertible at `ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} R₀)`
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_isIso_integral`). This is the
ambient form of blueprint `sk-lem-sbc-exchange-compatibility` (section `sec-smooth-base-change`)
used in the proof of `sk-thm-sbc-coefficients`, with no finiteness assumption on the square.

We also record the integral models of bounded constructible `ℚ̄_ℓ`-complexes on the ambient
derived categories (`ProEtale.CondensedRing.exists_padicAlgCl_iso_integralModel_obj`).

## Implementation notes

The base change maps `baseChangeMap Λ sq` and the exchange morphisms
`Adjunction.exchangeRight` of `nonempty_arrowIso_map_exchangeRight_derivedExtendScalars` agree
by definition, but their elaborations carry different proofs of instances such as
`EssentiallySmall Profinite` and `MonoidalPreadditive (Sheaf _ Ab)`; unifying them directly
times out. They are identified by `cast_proofs`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

/-- A morphism isomorphic as an arrow to the image of an isomorphism under a functor is an
isomorphism. -/
lemma isIso_of_arrow_mk_iso_map {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {W X : C} {Y Z : D} {f : W ⟶ X} {g : Y ⟶ Z} (e : Arrow.mk (F.map f) ≅ Arrow.mk g)
    (hf : IsIso f) : IsIso g :=
  ((MorphismProperty.isomorphisms D).arrow_mk_iso_iff e).1 (Functor.map_isIso F f)

section ExtendScalars

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The base change map under a flat change of coefficients**, on the ambient derived
categories: if `derivedPullIso a` is compatible with the composition of derived pullbacks and
the comparisons `derivedPushHom a f` at `K` and `derivedPushHom a f'` at `Lg'^* K` are
invertible, then the base change map with coefficients `Λ'` is invertible at `Λ' ⊗ᴸ_Λ K` as soon
as the one with coefficients `Λ` is invertible at `K`
(`nonempty_arrowIso_map_exchangeRight_derivedExtendScalars`). -/
theorem isIso_baseChangeMap_app_derivedExtendScalars (H : DerivedPullIsoCompCoherence a)
    (sq : CommSq g' f' f g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h₁ : IsIso ((derivedPushHom a f).app K))
    (h₂ : IsIso ((derivedPushHom a f').app ((g')^*⟦Λ⟧.leftDerivedFunctor.obj K)))
    (h : IsIso ((baseChangeMap Λ sq).app K)) :
    IsIso ((baseChangeMap Λ' sq).app
      ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K)) := by
  have h' : IsIso ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ f)
      (derivedUpperStarLowerStarAdjunction Λ f') (pullbackSquareComparison Λ sq)).app K) := by
    unfold baseChangeMap at h
    cast_proofs h
  have k : IsIso ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ' f)
      (derivedUpperStarLowerStarAdjunction Λ' f') (pullbackSquareComparison Λ' sq)).app
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K)) :=
    isIso_of_arrow_mk_iso_map _
      (nonempty_arrowIso_map_exchangeRight_derivedExtendScalars a H sq K h₁ h₂).some h'
  unfold baseChangeMap
  cast_proofs k

/-- The derived extension of scalars along a flat coefficient change, being exact, preserves
bounded below complexes. -/
lemma isGE_leftDerivedFunctor_extendScalars_obj (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (n : ℤ) [K.IsGE n] :
    ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K).IsGE n := by
  have := (Mod.extendScalars (coefficientMap a X)).isGE_mapDerivedCategory_obj K n
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((Functor.leftDerivedFunctorIsoMapDerivedCategory _).app K).symm n

end ExtendScalars

variable (ℓ : ℕ) [Fact ℓ.Prime]
variable (ℓ : ℕ) [Fact ℓ.Prime]

set_option maxHeartbeats 1000000 in
-- the coefficient rings of the two stages are unified
/-- **The base change map under the coefficient changes `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`**, on the ambient
derived categories: for a commutative square `g' ≫ p = p' ≫ g` of schemes with `p` and `p'`
quasi-compact and quasi-separated, if the base change map with coefficients `𝒪_E` is invertible
at a bounded below `R₀`, then the base change map with coefficients `ℚ̄_ℓ` is invertible at every
object isomorphic to `ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} R₀)`. The (Push) comparisons of both coefficient
changes are invertible on bounded below complexes
(`isIso_derivedPushHom_app_padicIntegers_of_isGE`,
`isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE`), so that
`isIso_baseChangeMap_app_derivedExtendScalars` applies twice. -/
theorem isIso_baseChangeMap_app_padicAlgCl_of_isIso_integral {X Y X' Y' : Scheme.{u}}
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X} [QuasiCompact p] [QuasiSeparated p]
    [QuasiCompact p'] [QuasiSeparated p'] (sq : CommSq g' p' p g) (E : FiniteIntermediateField ℓ)
    (R₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (n : ℤ) [R₀.IsGE n]
    (h : IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E.1) sq).app R₀))
    {A : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (e : (Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
      X)).leftDerivedFunctor.obj ((Mod.extendScalars (coefficientMap
        (padicIntegersRingObjToContinuousMapRingObj ℓ E) X)).leftDerivedFunctor.obj R₀) ≅ A) :
    IsIso ((baseChangeMap (Profinite.padicAlgClRingObj ℓ) sq).app A) := by
  have : ((g')^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.leftDerivedFunctor.obj R₀).IsGE n :=
    isGE_leftDerivedUpperStar_obj _ g' R₀ n
  have hE := isIso_baseChangeMap_app_derivedExtendScalars
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) (derivedPullIsoCompCoherence _) sq R₀
    (isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E p R₀ n)
    (isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E p' _ n) h
  have := isGE_leftDerivedFunctor_extendScalars_obj
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) X R₀ n
  have : ((g')^*⟦Profinite.continuousMapRingObj E.1⟧.leftDerivedFunctor.obj
      ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
        X)).leftDerivedFunctor.obj R₀)).IsGE n :=
    isGE_leftDerivedUpperStar_obj _ g' _ n
  have hΩ := isIso_baseChangeMap_app_derivedExtendScalars
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) (derivedPullIsoCompCoherence _) sq
    ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
      X)).leftDerivedFunctor.obj R₀)
    (isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E p _ n)
    (isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E p' _ n)
    (by cast_proofs hE)
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  cast_proofs hΩ

/-- **Integral models of `ℚ̄_ℓ`-complexes on the ambient derived categories**
(`ProEtale.exists_padicAlgCl_iso_integralModel`): every bounded constructible `ℚ̄_ℓ`-complex `K`
on a topologically noetherian scheme is isomorphic to `ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)` for a finite
subextension `E` and a bounded constructible `𝒪_E`-complex `K₀`, the extensions of scalars being
those of `isIso_baseChangeMap_app_padicAlgCl_of_isIso_integral`. -/
theorem exists_padicAlgCl_iso_integralModel_obj (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) K) :
    ∃ (E : FiniteIntermediateField ℓ)
      (K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)),
      Nonempty ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        X)).leftDerivedFunctor.obj ((Mod.extendScalars (coefficientMap
          (padicIntegersRingObjToContinuousMapRingObj ℓ E) X)).leftDerivedFunctor.obj K₀.obj) ≅
        K) := by
  have k := exists_padicAlgCl_iso_integralModel X ℓ ⟨K, hK⟩
  obtain ⟨E, K₀, he⟩ := k
  refine ⟨E, K₀, ⟨?_⟩⟩
  exact (derivedExtendScalarsToPadicAlgCl X ℓ E).mapIso
    ((boundedConstructibleExtendScalarsCompatibility X ℓ E).app K₀).symm ≪≫
    (boundedConstructible _).ι.mapIso he.some

end AlgebraicGeometry.ProEtale.CondensedRing
