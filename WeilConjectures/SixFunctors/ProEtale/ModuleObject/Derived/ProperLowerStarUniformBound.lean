/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdicBound
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarHeart

/-!
# A uniform bound for the proper direct image of ind-constructible sheaves

Let `ℓ` be a prime, `k` a field in which `ℓ` is invertible, `p : Z ⟶ Y` a proper morphism to a
`k`-scheme of finite type, and `d` a natural number bounding the dimensions of all geometric
fibres of `p`. For the coefficient rings `Λ = E` (a finite extension of `ℚ_ℓ`) and `Λ = ℚ̄_ℓ`, and
`M ∈ IndCons(Z, Λ)` (blueprint `lemma-uniform-bound-proper-direct-image--1`):

* `R^q p_* M = 0` for `q > 2d + 1` (we prove the sharper bound `Rp_* M ∈ D^{≤ 2d}`);
* `R^q p_* M ∈ IndCons(Y, Λ)` for `q ≥ 0`.

## Main results

All in the namespace `AlgebraicGeometry.ProEtale.CondensedRing`:

* `isIndConstructible_homology_rightDerivedLowerStar_singleFunctor_of_ind`: for a qcqs morphism
  and a flat coefficient ring, `R^q p_*` sends ind-constructible sheaves into `IndCons(Y, Λ)` as
  soon as it sends constructible sheaves into `Cons(Y, Λ)` (continuity of `R^q p_*`);
* `isLE_rightDerivedLowerStar_singleFunctor_continuousMapRingObj_of_isIndConstructible`,
  `isLE_rightDerivedLowerStar_singleFunctor_padicAlgClRingObj_of_isIndConstructible`: the bound
  `Rp_* M ∈ D^{≤ 2d}`;
* `rightDerivedLowerStar_uniformBound_continuousMapRingObj`,
  `rightDerivedLowerStar_uniformBound_padicAlgClRingObj`: the clause
  `lemma-uniform-bound-proper-direct-image--1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

section Continuity

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

omit [IsCommMonObj Λ] in
/-- For a quasi-compact quasi-separated morphism `f` and a flat coefficient ring `Λ`, if `R^q f_*`
sends the constructible sheaves into `Cons(Y, Λ)`, it sends `IndCons(Z, Λ)` into `IndCons(Y, Λ)`:
`R^q f_*` commutes with filtered colimits. -/
theorem isIndConstructible_homology_rightDerivedLowerStar_singleFunctor_of_ind
    {Z Y : Scheme.{u}} (f : Z ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [PreservesFiniteLimits (tensorLeft (condensedRingObj Λ Z))] (q : ℕ)
    (hP : ∀ N, IsConstructibleModuleObject (condensedRingObj Λ Z) N →
      IsConstructibleModuleObject (condensedRingObj Λ Y)
        ((DerivedCategory.homologyFunctor _ q).obj
          (R((f)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj N))))
    {M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)}
    (hM : IsIndConstructibleModuleObject (condensedRingObj Λ Z) M) :
    IsIndConstructibleModuleObject (condensedRingObj Λ Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        (R((f)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  obtain ⟨K, _, _, pres, hK⟩ := hM
  have := preservesColimitsOfShape_rightDerived_lowerStar f K q
  have := preservesColimitsOfShape_rightDerived_lowerStar_of_forget Λ f K q
  have : PreservesColimitsOfShape K (DerivedCategory.singleFunctor _ 0 ⋙ R((f)_*⟦Λ⟧) ⋙
      DerivedCategory.homologyFunctor _ q) :=
    preservesColimitsOfShape_of_natIso
      (((f)_*⟦Λ⟧).singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso q).symm
  exact ⟨K, inferInstance, inferInstance, pres.map (DerivedCategory.singleFunctor _ 0 ⋙
    R((f)_*⟦Λ⟧) ⋙ DerivedCategory.homologyFunctor _ q), fun i ↦ hP _ (hK i)⟩

end Continuity

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  (p : Z ⟶ Y) [IsProper p] (d : ℕ)
  (hd : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
    topologicalKrullDim (pullback p s : Scheme.{u}) ≤ (d : WithBot ℕ∞))

/-! ### The bound on constructible sheaves -/

include aY hd in
/-- For a finite subextension `E ⊆ ℚ̄_ℓ`, `Rp_*` sends the constructible `E`-sheaves into degrees
`≤ 2d`, `d` bounding the dimensions of the geometric fibres of `p` (blueprint
`lemma-uniform-bound-proper-direct-image--1`, constructible case). -/
lemma isLE_rightDerivedLowerStar_singleFunctor_finiteIntermediateField
    (E : FiniteIntermediateField ℓ)
    (N : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) Z))
    (hN : IsConstructibleModuleObject _ N) :
    ((R((p)_*⟦Profinite.continuousMapRingObj E.1⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE (2 * d : ℤ) := by
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType (p ≫ aY)
  obtain ⟨K₀, ⟨e⟩⟩ := exists_boundedConstructibleExtendScalars_obj_iso Z ℓ E
    ⟨_, boundedConstructible_singleFunctor_obj _ Z 0 N hN⟩
  have (X : Scheme.{u}) : PreservesFiniteLimits (Mod.extendScalars
      (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E) X)) :=
    preservesFiniteLimits_extendScalars_padicIntegersToPadicSubfield ℓ E X
  exact isLE_rightDerivedLowerStar_singleFunctor_of_extendScalars
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) p _
    (fun K n _ ↦ isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E p K n)
    (fun N₀ hN₀ ↦ by
      have := isLE_rightDerivedLowerStar_singleFunctor_padicIntegers_of_isProper ℓ E p d hd
        (residueFieldFiniteness_of_isNoetherian ℓ p aY E) N₀ hN₀
      exact_mod_cast this) K₀.obj
    K₀.property ((boundedConstructible _).ι.mapIso e)

include aY hd in
/-- For the coefficient ring `E` of a finite extension `E` of `ℚ_ℓ`, `Rp_*` sends the
constructible `E`-sheaves into degrees `≤ 2d`, `d` bounding the dimensions of the geometric fibres
of `p` (blueprint `lemma-uniform-bound-proper-direct-image--1`, constructible case). -/
lemma isLE_rightDerivedLowerStar_singleFunctor_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (N : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) Z))
    (hN : IsConstructibleModuleObject _ N) :
    ((R((p)_*⟦Profinite.continuousMapRingObj.{u} E⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE (2 * d : ℤ) := by
  obtain ⟨E', e, _⟩ := Profinite.exists_continuousMapRingObj_iso.{u} ℓ E
  exact isLE_rightDerivedLowerStar_singleFunctor_of_iso e p _
    (isLE_rightDerivedLowerStar_singleFunctor_finiteIntermediateField ℓ aY p d hd E') N hN

include aY hd in
/-- For the coefficient ring `ℚ̄_ℓ`, `Rp_*` sends the constructible `ℚ̄_ℓ`-sheaves into degrees
`≤ 2d`, `d` bounding the dimensions of the geometric fibres of `p` (blueprint
`lemma-uniform-bound-proper-direct-image--1`, constructible case). -/
lemma isLE_rightDerivedLowerStar_singleFunctor_padicAlgClRingObj
    (N : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z))
    (hN : IsConstructibleModuleObject _ N) :
    ((R((p)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE (2 * d : ℤ) := by
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType (p ≫ aY)
  obtain ⟨E, K_E, ⟨e⟩⟩ := constructibleCocone_essSurjObj Z ℓ
    ⟨_, boundedConstructible_singleFunctor_obj _ Z 0 N hN⟩
  have (X : Scheme.{u}) : PreservesFiniteLimits (Mod.extendScalars
      (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X)) :=
    preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl ℓ X E
  exact isLE_rightDerivedLowerStar_singleFunctor_of_extendScalars
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) p _
    (fun K n _ ↦ isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E p K n)
    (isLE_rightDerivedLowerStar_singleFunctor_finiteIntermediateField ℓ aY p d hd E)
    K_E.obj K_E.property ((boundedConstructible _).ι.mapIso e)

/-! ### The bound on ind-constructible sheaves -/

include aY hd in
/-- Blueprint `lemma-uniform-bound-proper-direct-image--1`, amplitude, for the coefficient ring
`E` of a finite extension `E` of `ℚ_ℓ`: `Rp_*` sends `IndCons(Z, E)` into degrees `≤ 2d`. -/
lemma isLE_rightDerivedLowerStar_singleFunctor_continuousMapRingObj_of_isIndConstructible
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    {M : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) Z)}
    (hM : IsIndConstructibleModuleObject _ M) :
    ((R((p)_*⟦Profinite.continuousMapRingObj.{u} E⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE (2 * d : ℤ) := by
  obtain ⟨E', e, _⟩ := Profinite.exists_continuousMapRingObj_iso.{u} ℓ E
  have : PreservesFiniteLimits
      (tensorLeft (condensedRingObj (Profinite.continuousMapRingObj.{u} E) Z)) :=
    preservesFiniteLimits_of_natIso
      ((curriedTensor _).mapIso ((upperStarFromPoint Z).mapIso e.symm))
  exact isLE_rightDerivedLowerStar_singleFunctor_of_ind _ p _ _
    (isLE_rightDerivedLowerStar_singleFunctor_continuousMapRingObj ℓ aY p d hd E) hM

include aY hd in
/-- Blueprint `lemma-uniform-bound-proper-direct-image--1`, amplitude, for the coefficient ring
`ℚ̄_ℓ`: `Rp_*` sends `IndCons(Z, ℚ̄_ℓ)` into degrees `≤ 2d`. -/
lemma isLE_rightDerivedLowerStar_singleFunctor_padicAlgClRingObj_of_isIndConstructible
    {M : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Z)}
    (hM : IsIndConstructibleModuleObject _ M) :
    ((R((p)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE (2 * d : ℤ) :=
  isLE_rightDerivedLowerStar_singleFunctor_of_ind _ p _ _
    (isLE_rightDerivedLowerStar_singleFunctor_padicAlgClRingObj ℓ aY p d hd) hM

/-! ### Ind-constructibility of the higher direct images -/

include aY in
/-- Blueprint `lemma-uniform-bound-proper-direct-image--1`, second assertion, for the coefficient
ring `E` of a finite extension `E` of `ℚ_ℓ`: `R^q p_* M ∈ IndCons(Y, E)` for
`M ∈ IndCons(Z, E)`. -/
lemma isIndConstructible_homology_rightDerivedLowerStar_continuousMapRingObj
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    {M : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) Z)}
    (hM : IsIndConstructibleModuleObject _ M) (q : ℤ) :
    IsIndConstructibleModuleObject _ ((DerivedCategory.homologyFunctor _ q).obj
      ((R((p)_*⟦Profinite.continuousMapRingObj.{u} E⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  rcases lt_or_ge q 0 with hq | hq
  · have := ((p)_*⟦Profinite.continuousMapRingObj.{u} E⟧).isGE_rightDerivedFunctor_obj_singleFunctor
      M
    exact ObjectProperty.prop_of_isZero _ (DerivedCategory.isZero_of_isGE _ 0 q hq)
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
  obtain ⟨E', e, _⟩ := Profinite.exists_continuousMapRingObj_iso.{u} ℓ E
  have : PreservesFiniteLimits
      (tensorLeft (condensedRingObj (Profinite.continuousMapRingObj.{u} E) Z)) :=
    preservesFiniteLimits_of_natIso
      ((curriedTensor _).mapIso ((upperStarFromPoint Z).mapIso e.symm))
  exact isIndConstructible_homology_rightDerivedLowerStar_singleFunctor_of_ind _ p n
    (fun N hN ↦ (boundedConstructible_rightDerivedLowerStar_obj_of_isProper_continuousMapRingObj
      ℓ E aY p _ (boundedConstructible_singleFunctor_obj _ Z 0 N hN)).2 n) hM

include aY in
/-- Blueprint `lemma-uniform-bound-proper-direct-image--1`, second assertion, for the coefficient
ring `ℚ̄_ℓ`: `R^q p_* M ∈ IndCons(Y, ℚ̄_ℓ)` for `M ∈ IndCons(Z, ℚ̄_ℓ)`. -/
lemma isIndConstructible_homology_rightDerivedLowerStar_padicAlgClRingObj
    {M : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Z)}
    (hM : IsIndConstructibleModuleObject _ M) (q : ℤ) :
    IsIndConstructibleModuleObject _ ((DerivedCategory.homologyFunctor _ q).obj
      ((R((p)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  rcases lt_or_ge q 0 with hq | hq
  · have := ((p)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧).isGE_rightDerivedFunctor_obj_singleFunctor
      M
    exact ObjectProperty.prop_of_isZero _ (DerivedCategory.isZero_of_isGE _ 0 q hq)
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
  exact isIndConstructible_homology_rightDerivedLowerStar_singleFunctor_of_ind _ p n
    (fun N hN ↦ (boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicAlgClRingObj
      ℓ aY p _ (boundedConstructible_singleFunctor_obj _ Z 0 N hN)).2 n) hM

/-! ### The clause `lemma-uniform-bound-proper-direct-image--1` -/

include aY hd in
/-- Blueprint `lemma-uniform-bound-proper-direct-image--1`, for the coefficient ring `E` of a
finite extension `E` of `ℚ_ℓ`: let `p : Z ⟶ Y` be proper, `Y` of finite type over `k`, and `d`
bound the dimensions of all geometric fibres of `p`. For `M ∈ IndCons(Z, E)`,
`R^q p_* M = 0` for `q > 2d + 1` and `R^q p_* M ∈ IndCons(Y, E)` for `q ≥ 0`. -/
theorem rightDerivedLowerStar_uniformBound_continuousMapRingObj
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (M : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) Z))
    (hM : IsIndConstructibleModuleObject _ M) :
    (∀ q : ℤ, 2 * (d : ℤ) + 1 < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((R((p)_*⟦Profinite.continuousMapRingObj.{u} E⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)))) ∧
    ∀ q : ℤ, 0 ≤ q → IsIndConstructibleModuleObject _ ((DerivedCategory.homologyFunctor _ q).obj
      ((R((p)_*⟦Profinite.continuousMapRingObj.{u} E⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  have := isLE_rightDerivedLowerStar_singleFunctor_continuousMapRingObj_of_isIndConstructible
    ℓ aY p d hd E hM
  exact ⟨fun q hq ↦ DerivedCategory.isZero_of_isLE _ (2 * d : ℤ) q (by lia),
    fun q _ ↦ isIndConstructible_homology_rightDerivedLowerStar_continuousMapRingObj ℓ aY p E hM q⟩

include aY hd in
/-- Blueprint `lemma-uniform-bound-proper-direct-image--1`, for the coefficient ring `ℚ̄_ℓ`: let
`p : Z ⟶ Y` be proper, `Y` of finite type over `k`, and `d` bound the dimensions of all
geometric fibres of `p`. For `M ∈ IndCons(Z, ℚ̄_ℓ)`, `R^q p_* M = 0` for `q > 2d + 1` and
`R^q p_* M ∈ IndCons(Y, ℚ̄_ℓ)` for `q ≥ 0`. -/
theorem rightDerivedLowerStar_uniformBound_padicAlgClRingObj
    (M : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Z))
    (hM : IsIndConstructibleModuleObject _ M) :
    (∀ q : ℤ, 2 * (d : ℤ) + 1 < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((R((p)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)))) ∧
    ∀ q : ℤ, 0 ≤ q → IsIndConstructibleModuleObject _ ((DerivedCategory.homologyFunctor _ q).obj
      ((R((p)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  have := isLE_rightDerivedLowerStar_singleFunctor_padicAlgClRingObj_of_isIndConstructible
    ℓ aY p d hd hM
  exact ⟨fun q hq ↦ DerivedCategory.isZero_of_isLE _ (2 * d : ℤ) q (by lia),
    fun q _ ↦ isIndConstructible_homology_rightDerivedLowerStar_padicAlgClRingObj ℓ aY p hM q⟩

end AlgebraicGeometry.ProEtale.CondensedRing
