/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistData
import Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistSectionRestriction
import Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistLocalizationProduct

/-! Multiplication part of the normalized scalar-extension twist laws.
(blueprint: lem-sfb-proj-scalar-extension-twist-fraction-laws-multiplication). -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/- The chartwise fraction calculation proves this product clause. -/
theorem scalarExtension_twist_multiplication
    {A B : Type u} [CommRing A] [CommRing B]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ) (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j)
    (hθ : IsScalarExtensionTwistComparison ψ r θ) :
    ∀ (i j : ℤ) (U : (Proj 𝒜).Opens)
      (s : Γ(twist 𝒜 i, U)) (t : Γ(twist 𝒜 j, U))
      (v : Γ(twist 𝒜 (i + j), U)),
      (∀ x : U, (v.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
        (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * t.1 x) →
      ∀ x : r ⁻¹ᵁ U,
        ((scalarExtensionTwistSection r θ (i + j) U v).1 x :
          Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
        ((scalarExtensionTwistSection r θ i U s).1 x :
          Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
        (scalarExtensionTwistSection r θ j U t).1 x := by
  intro i j U s t v hv x
  have hs := s.2 ⟨_, x.2⟩
  obtain ⟨V, hyV, e, ai, ak, hik, a, b, hb, hsval⟩ := hs
  let sV : Γ(twist 𝒜 i, V) := (twist 𝒜 i).presheaf.map e.op s
  let xV : r ⁻¹ᵁ V := ⟨x.1, hyV⟩
  have hVb : V ≤ basicOpen 𝒜 (b : A) := by
    intro y hy
    exact hb ⟨y, hy⟩
  have hsfrac : ∀ y : V, (sV.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
      Localization.mk (b : A) 1 = Localization.mk (a : A) 1 := by
    intro y
    change (s.1 (e y) : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
      Localization.mk (b : A) 1 = Localization.mk (a : A) 1
    have hsy := hsval y
    change (s.1 (e y) : _) = _ at hsy
    rw [hsy, HomogeneousLocalization.degreePart.coe_mk]
    rw [Localization.mk_mul]
    simpa using localization_mk_mul_denominator
      (P := y.1.asHomogeneousIdeal.toIdeal) (a := (a : A)) (b := (b : A)) (hb := hb y)
  have hsf := hθ i ai ak a b a.2 b.2 hik V hVb sV hsfrac
    (1 : Γ(Proj ℬ, r ⁻¹ᵁ V)) xV
  have hsres := scalarExtensionTwistSection_restrict r θ i U V e.le s xV
  have hsres' : (scalarExtensionTwistSection r θ i V sV).1 xV =
      (scalarExtensionTwistSection r θ i U s).1 x := by
    have he : homOfLE e.le = e := Subsingleton.elim _ _
    simpa [sV, xV, he] using hsres
  sorry

end AlgebraicGeometry.Proj
