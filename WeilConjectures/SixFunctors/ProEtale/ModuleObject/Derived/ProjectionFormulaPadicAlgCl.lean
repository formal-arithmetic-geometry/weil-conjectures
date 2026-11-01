/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModelPair
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.CategoryTheory.NatIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite
public import WeilConjectures.Tactic.ExactModProofs

/-!
# The `ℚ̄_ℓ` projection formula from the integral one

Let `p : X ⟶ Y` be a morphism of separated `k`-schemes of finite type, `ℓ ≠ char k`. If the
projection map `Rp_* K ⊗ᴸ M ⟶ Rp_*(K ⊗ᴸ Lp^* M)` is an isomorphism for bounded constructible
`𝒪_E`-complexes, for every finite subextension `E ⊆ ℚ̄_ℓ`, then it is an isomorphism for bounded
constructible `ℚ̄_ℓ`-complexes
(`ProEtale.CondensedRing.isIso_projectionMap_padicAlgClRingObj_of_integral`, blueprint
`det-thm-sfb-proper-base-change-rational` (3)).

Bounded constructible `ℚ̄_ℓ`-complexes `K` and `M` have integral models `K₀`, `M₀` over a common
`𝒪_E` (`ProEtale.exists_padicAlgCl_iso_integralModel_pair`): `K ≅ ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)`.
The extensions of scalars `𝒪_E ⟶ E` and `E ⟶ ℚ̄_ℓ` are flat, and the (Push) comparisons
`T Rp_* ⟶ Rp_* T` are isomorphisms on bounded below objects
(`ProEtale.CondensedRing.isIso_projectionMap_app_app_padicSubfield_of_padicIntegers`,
`ProEtale.CondensedRing.isIso_projectionMap_app_app_padicAlgCl_of_padicSubfield`), so the
projection formula is transported along both of them
(`ProEtale.CondensedRing.isIso_projectionMap_app_app_extendScalars`).

The concrete coefficient rings carry instance arguments elaborated in different contexts, which
differ by proofs only; comparing them with the unifier times out, and the tactic
`exact_mod_proofs` bridges them.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A bounded constructible complex is bounded below. -/
lemma exists_isGE_of_boundedConstructible {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)}
    (hK : boundedConstructible R K) : ∃ n : ℤ, K.IsGE n := by
  obtain ⟨⟨n, hn⟩, -⟩ := hK.1
  exact ⟨n, hn⟩

namespace CondensedRing

open Scheme PadicAlgCl

/-- `isIso_projectionMap_app_app_extendScalars` with explicit hypotheses, the projection map with
coefficients `Λ` last. -/
lemma isIso_projectionMap_app_app_extendScalars_of_isIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
    [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (h₁ : IsIso ((derivedPushHom a f).app K))
    (h₂ : IsIso ((derivedPushHom a f).app
      (((curriedTensor _).obj K).obj (((f)^*⟦Λ⟧).leftDerivedFunctor.obj M))))
    (h₀ : IsIso (((projectionMap Λ f).app K).app M)) :
    IsIso (((projectionMap Λ' f).app
      ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K)).app
        ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj M)) :=
  isIso_projectionMap_app_app_extendScalars a f K M

section ExtendScalars

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ) {X Y : Scheme.{u}} (f : X ⟶ Y)
  [QuasiCompact f] [QuasiSeparated f]

/-- **The projection formula and the coefficient change `𝒪_E ⟶ E`**: for a quasi-compact
quasi-separated `f`, if the projection map with coefficients `𝒪_E` is invertible at `(K₀, M₀)`,
with `K₀` and `K₀ ⊗ᴸ Lf^* M₀` bounded below, then the projection map with coefficients `E` is
invertible at `(E ⊗ᴸ K₀, E ⊗ᴸ M₀)`. -/
theorem isIso_projectionMap_app_app_padicSubfield_of_padicIntegers
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (M₀ : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)))
    (n m : ℤ) (hn : K₀.IsGE n)
    (hm : (((curriedTensor _).obj K₀).obj
      (((f)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).leftDerivedFunctor.obj M₀)).IsGE m)
    (h : IsIso (((projectionMap (Profinite.padicIntegersRingObj ℓ E.1) f).app K₀).app M₀)) :
    IsIso (((projectionMap (Profinite.continuousMapRingObj E.1) f).app
      ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
        X)).leftDerivedFunctor.obj K₀)).app
      ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
        Y)).leftDerivedFunctor.obj M₀)) := by
  have e := isIso_projectionMap_app_app_extendScalars_of_isIso
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) f K₀ M₀
    (by exact_mod_proofs isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E f K₀ n)
    (by exact_mod_proofs (isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E f
      (((curriedTensor _).obj K₀).obj
        (((f)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).leftDerivedFunctor.obj M₀)) m))
    (by exact_mod_proofs h)
  exact_mod_proofs e

/-- **The projection formula and the coefficient change `E ⟶ ℚ̄_ℓ`**: for a quasi-compact
quasi-separated `f`, if the projection map with coefficients `E` is invertible at `(K, M)`, with
`K` and `K ⊗ᴸ Lf^* M` bounded below, then the projection map with coefficients `ℚ̄_ℓ` is
invertible at `(ℚ̄_ℓ ⊗ᴸ K, ℚ̄_ℓ ⊗ᴸ M)`. -/
theorem isIso_projectionMap_app_app_padicAlgCl_of_padicSubfield
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X)))
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) Y)))
    (n m : ℤ) (hn : K.IsGE n)
    (hm : (((curriedTensor _).obj K).obj
      (((f)^*⟦Profinite.continuousMapRingObj E.1⟧).leftDerivedFunctor.obj M)).IsGE m)
    (h : IsIso (((projectionMap (Profinite.continuousMapRingObj E.1) f).app K).app M)) :
    IsIso (((projectionMap (Profinite.padicAlgClRingObj ℓ) f).app
      ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        X)).leftDerivedFunctor.obj K)).app
      ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        Y)).leftDerivedFunctor.obj M)) := by
  have e := isIso_projectionMap_app_app_extendScalars_of_isIso
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f K M
    (by exact_mod_proofs
      isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E f K n)
    (by exact_mod_proofs (isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E f
      (((curriedTensor _).obj K).obj
        (((f)^*⟦Profinite.continuousMapRingObj E.1⟧).leftDerivedFunctor.obj M)) m))
    (by exact_mod_proofs h)
  exact_mod_proofs e

end ExtendScalars

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

set_option maxHeartbeats 1000000 in
-- the concrete coefficient rings are unfolded when comparing elaborations from different files
/-- **The `ℚ̄_ℓ` projection formula from the integral one**: if the projection map
`Rp_* K ⊗ᴸ M ⟶ Rp_*(K ⊗ᴸ Lp^* M)` is an isomorphism on bounded constructible `𝒪_E`-complexes for
every finite subextension `E ⊆ ℚ̄_ℓ`, it is an isomorphism on bounded constructible
`ℚ̄_ℓ`-complexes. -/
theorem isIso_projectionMap_padicAlgClRingObj_of_integral (p : X ⟶ Y)
    (h : ∀ (E : FiniteIntermediateField ℓ)
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left)))
      (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y.left))),
      boundedConstructible _ K → boundedConstructible _ M →
        IsIso (((projectionMap (Profinite.padicIntegersRingObj ℓ E.1) p.left).app K).app M))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)))
    (hK : boundedConstructible _ K) (hM : boundedConstructible _ M) :
    IsIso (((projectionMap (Profinite.padicAlgClRingObj ℓ) p.left).app K).app M) := by
  have := isNoetherian_of_locallyOfFiniteType X.hom
  have := isNoetherian_of_locallyOfFiniteType Y.hom
  have : QuasiCompact p.left :=
    have : QuasiCompact (p.left ≫ Y.hom) := by rw [Over.w p]; infer_instance
    QuasiCompact.of_comp p.left Y.hom
  have : QuasiSeparated p.left :=
    have : QuasiSeparated (p.left ≫ Y.hom) := by rw [Over.w p]; infer_instance
    QuasiSeparated.of_comp p.left Y.hom
  obtain ⟨E, K₀, M₀, eK, eM⟩ :=
    exists_derivedExtendScalars_iso_integralModel_pair X.left Y.left ℓ ⟨K, hK⟩ ⟨M, hM⟩
  -- bounded below complexes
  have hKM₀ := (PadicIntegersRingObj.isMonoidal_boundedConstructible ℓ E.1 X).toTensorLE.prop_tensor
    _ _ K₀.property (boundedConstructible_leftDerivedUpperStar_obj _ ℓ p M₀)
  have hK₁ := boundedConstructible_derivedExtendScalars_obj X.left ℓ E K₀
  have hM₁ := boundedConstructible_derivedExtendScalars_obj Y.left ℓ E M₀
  have hKM₁ := (ContinuousMapRingObj.isMonoidal_boundedConstructible ℓ E X).toTensorLE.prop_tensor
    _ _ hK₁ (boundedConstructible_leftDerivedUpperStar_obj _ ℓ p ⟨_, hM₁⟩)
  -- the changes of coefficients `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`
  have e₁ := isIso_projectionMap_app_app_padicSubfield_of_padicIntegers ℓ E p.left K₀.obj M₀.obj
    _ _ (exists_isGE_of_boundedConstructible K₀.property).choose_spec
    (by exact_mod_proofs (exists_isGE_of_boundedConstructible hKM₀).choose_spec)
    (by exact_mod_proofs h E K₀.obj M₀.obj K₀.property M₀.property)
  have e₂ := isIso_projectionMap_app_app_padicAlgCl_of_padicSubfield ℓ E p.left
    ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
      X.left)).leftDerivedFunctor.obj K₀.obj)
    ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
      Y.left)).leftDerivedFunctor.obj M₀.obj)
    (exists_isGE_of_boundedConstructible hK₁).choose
    (exists_isGE_of_boundedConstructible hKM₁).choose
    (by exact_mod_proofs (exists_isGE_of_boundedConstructible hK₁).choose_spec)
    (by exact_mod_proofs (exists_isGE_of_boundedConstructible hKM₁).choose_spec)
    (by exact_mod_proofs e₁)
  have e₃ := @NatTrans.isIso_app_app_of_iso _ _ _ _ _ _ _ _
    (projectionMap (Profinite.padicAlgClRingObj ℓ) p.left) _ _ _ _ eK.some eM.some
    (by exact_mod_proofs e₂)
  exact_mod_proofs e₃

end CondensedRing

end AlgebraicGeometry.ProEtale
