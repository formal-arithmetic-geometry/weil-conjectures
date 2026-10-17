/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Torsion
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.QuotPowTriangle
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative

/-!
# The reductions of the projection map are isomorphisms

Let `Λ` be a principal ideal domain, `ϖ` a nonzerodivisor of `Λ` and `n` such that some nonzero
integer lies in `(ϖⁿ)`; for `Λ = 𝒪_E` and `ϖ` a uniformizer this holds for every `n`. For
`f : X ⟶ Y` admitting a compactification, `K` bounded of finite Tor amplitude and `L` bounded
constructible, the reduction `ρ(PF_{f, K, L}) = PF_{f, K, L} ⊗ᴸ (Λ/ϖⁿ)_Y` of the projection map
is an isomorphism. This is the reduction step of blueprint `sk-thm-sf-pf-adic` (Steps 1 and 2 of
its proof, with `sk-prop-sf-pf-reduction` and the finite-level projection formula
`sk-thm-sf-pf-finite`): the reduction is moved onto the first variable
(`AlgebraicGeometry.Etale.isIso_derivedTensorRight_map_projectionMapOfCompactification_of_tensor`),
where `K ⊗ᴸ (Λ/ϖⁿ)_X` is torsion, and the projection formula for torsion objects
(`AlgebraicGeometry.Etale.hasProjectionFormulaOfCompactification_of_nsmul_id_eq_zero`) applies.

## Main statements

- `AlgebraicGeometry.Etale.isIso_reductionModIdeal_map_projectionMap_of_nsmul`
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)`. -/
local notation "𝐃(" X ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-- The reduction modulo `ϖⁿ` lowers the lower bound of an object by at most one: it is the cone
of the multiplication by `ϖⁿ`. -/
lemma isGE_reductionModIdeal_obj {X : Scheme.{u}} {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (n : ℕ) (T : 𝐃(X)) (a : ℤ) [T.IsGE a] :
    ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj T).IsGE (a - 1) := by
  let F := (derivedTensor (ModuleCat.{u + 1} Λ) X).obj T
  let Tr := _root_.DerivedCategory.quotPowTriangle X.smallEtaleTopology hϖ rfl n
  have hT := rot_of_distTriang _ (F.map_distinguished _
    (_root_.DerivedCategory.quotPowTriangle_distinguished X.smallEtaleTopology hϖ rfl n))
  have h₁ : (F.obj Tr.obj₂).IsGE (a - 1) := by
    have : T.IsGE (a - 1) := _root_.DerivedCategory.TStructure.t.isGE_of_ge T (a - 1) a (by lia)
    exact _root_.DerivedCategory.TStructure.t.isGE_of_iso (derivedTensorSingleUnitIso T).symm
      (a - 1)
  have h₃ : ((F.obj Tr.obj₁)⟦(1 : ℤ)⟧).IsGE (a - 1) := by
    have : (F.obj Tr.obj₁).IsGE a :=
      _root_.DerivedCategory.TStructure.t.isGE_of_iso (derivedTensorSingleUnitIso T).symm a
    exact _root_.DerivedCategory.TStructure.t.isGE_shift _ a 1 (a - 1) (by lia)
  exact _root_.DerivedCategory.TStructure.t.isGE₂ _ hT (a - 1) h₁ h₃

/-- **The reductions of the projection map are isomorphisms.** Let `Λ` be a principal ideal
domain, `ϖ` a nonzerodivisor and `N ≠ 0` an integer lying in `(ϖⁿ)`. For `f` admitting a
compactification, `K` bounded of finite Tor amplitude and `L` bounded constructible, the
reduction `PF_{f, K, L} ⊗ᴸ (Λ/ϖⁿ)_Y` of the projection map is an isomorphism. -/
theorem isIso_reductionModIdeal_map_projectionMap_of_nsmul [IsPrincipalIdealRing Λ]
    [IsDomain Λ] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) {N : ℕ} (hN : N ≠ 0)
    (hNJ : (N : Λ) ∈ Ideal.span {ϖ} ^ n) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (K : 𝐃(X)) (L : 𝐃(Y))
    (hKb : _root_.DerivedCategory.TStructure.t.bounded K)
    (hKt : DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} Λ) X K)
    (hL : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y L) :
    IsIso ((reductionModIdeal Λ Y (Ideal.span {ϖ} ^ n)).map
      (((projectionMap (ModuleCat.{u + 1} Λ) f).app K).app L)) := by
  obtain ⟨⟨k, hk⟩, -⟩ := hKb
  obtain ⟨a, b, hab⟩ := hKt
  let J := Ideal.span {ϖ} ^ n
  let c := HasCompactification.compactification f
  let M := (L((f)^*[ModuleCat.{u + 1} Λ])).obj L
  obtain ⟨⟨m, hm⟩, hm'⟩ := (boundedConstructible_leftDerivedUpperStar _ f hL).1
  -- `K ⊗ᴸ Lf^* L` is bounded below, by the Tor amplitude of `K`
  have hKM : (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M).IsGE (m + a) :=
    _root_.DerivedCategory.isGE_obj_of_isGE ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K) a
      (fun F ↦ ((_root_.DerivedCategory.homologyConcentratedIn_iff _ _ _).1 (hab F)).1) M
      ⟨⟨m, hm⟩, hm'⟩ m
  let K' := (reductionModIdeal Λ X J).obj K
  have hK' : N • 𝟙 K' = 0 := nsmul_id_reductionModIdeal hNJ K
  have : K'.IsGE (k - 1) := isGE_reductionModIdeal_obj hϖ n K k
  have : ((reductionModIdeal Λ X J).obj
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M)).IsGE (m + a - 1) :=
    isGE_reductionModIdeal_obj hϖ n _ (m + a)
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let NX := constantSingle (ModuleCat.{u + 1} Λ) X (ModuleCat.of Λ (Λ ⧸ J))
  let e : (K ⊗ NX) ⊗ M ≅ (K ⊗ M) ⊗ NX :=
    α_ K NX M ≪≫ whiskerLeftIso K (β_ NX M) ≪≫ (α_ K M NX).symm
  have : (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K').obj M).IsGE (m + a - 1) :=
    _root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm (m + a - 1)
  have h : HasProjectionFormulaOfCompactification (ModuleCat.{u + 1} Λ) c K' L :=
    hasProjectionFormulaOfCompactification_of_nsmul_id_eq_zero c K' L hN hK' (k - 1)
      (m + a - 1) hL
  exact isIso_derivedTensorRight_map_projectionMapOfCompactification_of_tensor _ c
    (leftDerivedUpperStarSingleConstantSheafIso _ f (ModuleCat.of Λ (Λ ⧸ J)))
    (isDualizable_constantSingle_quotient_span_pow hϖ n Y) K L h

end Etale

end AlgebraicGeometry
