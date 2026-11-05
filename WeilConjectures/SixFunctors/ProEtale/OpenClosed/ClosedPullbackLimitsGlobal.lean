/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedLiftSections

/-!
# The closed inverse image preserves limits: the global case

Let `X` be quasi-compact and quasi-separated, and `i : Z ⟶ X` a closed immersion with
quasi-compact open complement `j`. The pullback `i^*` of pro-étale sheaves of modules preserves
all small limits (`AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_of_isCompl`,
blueprint `det-sf-open-closed-pullback-limits`). The affine case `X = Spec A` is
`AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_closedSpecι`; in general the
comparison map `i^* lim F ⟶ lim i^* F` is an isomorphism after restriction to the closed fibres
of the members of a finite affine open cover of `X`, which jointly detect isomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {R : Type (u + 1)} [Ring R]

/-- The pullback along a weakly étale monomorphism (e.g. an open immersion or an isomorphism)
preserves limits: it is the restriction to the localized site, a right adjoint. -/
lemma preservesLimitsOfSize_upperStar_of_mono {Y X : Scheme.{u}} (g : Y ⟶ X) [WeaklyEtale g]
    [Mono g] : PreservesLimitsOfSize.{u + 1, u + 1} ((g)^*[ModuleCat.{u + 1} R]) :=
  preservesLimits_of_natIso (upperStarIsoLocalizationRestriction _ g inferInstance).symm

/-- A morphism of pro-étale sheaves of modules whose pullbacks along finitely many quasi-compact
morphisms jointly covering the base are isomorphisms is an isomorphism. -/
lemma isIso_of_forall_isIso_upperStar_map {U : Scheme.{u}} {κ : Type*} [Finite κ]
    {Z : κ → Scheme.{u}} (g : ∀ k, Z k ⟶ U) [∀ k, QuasiCompact (g k)]
    (hg : ∀ x, ∃ k, x ∈ Set.range (g k)) {F G : Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R)}
    (φ : F ⟶ G) (h : ∀ k, IsIso ((g k)^*[ModuleCat.{u + 1} R].map φ)) : IsIso φ := by
  have hzero : ∀ E : Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R),
      (∀ k, IsZero ((g k)^*[ModuleCat.{u + 1} R].obj E)) → IsZero E := fun E hE ↦
    (IsZero.iff_id_eq_zero E).2 (eq_zero_of_forall_upperStar_map_eq_zero R g hg (𝟙 E)
      fun k ↦ (hE k).eq_of_src _ _)
  have : Mono φ := Preadditive.mono_of_isZero_kernel _ (hzero _ fun k ↦
    have := h k
    (isZero_kernel_of_mono ((g k)^*[ModuleCat.{u + 1} R].map φ)).of_iso
      (PreservesKernel.iso _ φ))
  have : Epi φ := Preadditive.epi_of_isZero_cokernel _ (hzero _ fun k ↦
    have := h k
    (isZero_cokernel_of_epi ((g k)^*[ModuleCat.{u + 1} R].map φ)).of_iso
      (PreservesCokernel.iso _ φ))
  exact isIso_of_mono_of_epi φ

/-- The pullback along a composite `h₁ ≫ h₂` preserves limits if the pullbacks along `h₁` and
`h₂` do. -/
lemma preservesLimitsOfSize_upperStar_comp {T S X : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ X)
    [PreservesLimitsOfSize.{u + 1, u + 1} ((h₁)^*[ModuleCat.{u + 1} R])]
    [PreservesLimitsOfSize.{u + 1, u + 1} ((h₂)^*[ModuleCat.{u + 1} R])] :
    PreservesLimitsOfSize.{u + 1, u + 1} ((h₁ ≫ h₂)^*[ModuleCat.{u + 1} R]) :=
  preservesLimits_of_natIso (upperStarComp _ h₁ h₂).symm

variable {Z U : Scheme.{u}}

end ProEtale

end AlgebraicGeometry
