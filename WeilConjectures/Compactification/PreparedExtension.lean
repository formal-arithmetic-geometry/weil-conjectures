/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BoundaryPreparation
public import WeilConjectures.Compactification.CompactifiedProperExtension
public import WeilConjectures.Compactification.GraphExtension

/-!

# Existence of a prepared side of the two-open compactification theorem

`AlgebraicGeometry.exists_prepared_compactifiedProperExtension` builds, for a
compactifiable open `O` of `U` covering `U` together with a second open `O'`, a
compactified proper extension of `O` along `u : U ⟶ S` whose two boundary closures are
disjoint (blueprint: `def:nagata-two-open-dense-compactifications` through
`lemma:nagata-prepared-boundaries`; proof order items 34–36).

The construction chains the three inputs of the blueprint: a scheme-theoretically dense
compactification of `O ⟶ S` (`exists_compactification_isSchemeTheoreticallyDominant`),
its graph extension to a proper morphism to `U` (Stacks Project Tag 0F3Z,
`Compactification.nonempty_properExtension`), and the constructible-boundary separation
blow-up which separates the two boundary closures (Stacks Project Tags 080P and 0F3V,
`exists_admissibleBlowup_disjoint_closures`).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {U S : Scheme.{u}}

/-- **Existence of a prepared side** (blueprint:
`def:nagata-two-open-dense-compactifications` through
`lemma:nagata-prepared-boundaries`; proof order items 34–36).

Choose a scheme-theoretically dense compactification of `O ⟶ S`, extend it to a proper
morphism to `U` by the graph construction (Stacks Project Tag 0F3Z), and separate the
two boundary closures by the boundary-separation blow-up (Stacks Project Tag 0F3V). -/
theorem exists_prepared_compactifiedProperExtension [IsNoetherian S] (u : U ⟶ S)
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u] (O O' : U.Opens)
    (hcov : O ⊔ O' = ⊤) [HasCompactification (O.ι ≫ u)] :
    ∃ σ : CompactifiedProperExtension u O, σ.Prepared O' := by
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian u
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace u
  have : IsNoetherian U := ⟨⟩
  have : QuasiCompact (O.ι ≫ u) := inferInstance
  -- item 34: a scheme-theoretically dense compactification of `O ⟶ S`
  obtain ⟨c, hc⟩ := exists_compactification_isSchemeTheoreticallyDominant (O.ι ≫ u)
  have : IsNoetherian c.Z := isNoetherian_of_isProper c.g
  -- Stacks 0F3Z: the graph extension of the compactification
  obtain ⟨B, Vgr, ψ, v, hψ, hv, hvπ, hvψ, -, hiso, hψu⟩ :=
    (Compactification.nonempty_properExtension u O
      (TopologicalSpace.NoetherianSpace.isCompact _) c).some
  have := hψ
  have := hv
  have := B.isProper_blowupMap
  -- the graph-extension side
  have hdense : IsSchemeTheoreticallyDominant (v ≫ Vgr.ι) := by
    have hq : (v ≫ Vgr.ι) ≫ B.I.blowupMap = c.i := by rw [Category.assoc, hvπ]
    have : IsSchemeTheoreticallyDominant c.i.opensRange.ι :=
      (isSchemeTheoreticallyDominant_iff_opensRange_ι c.i).mp hc
    have : IsIso (B.I.blowupMap ∣_ c.i.opensRange) := B.isIso_blowupMap_restrict
    have : IsSchemeTheoreticallyDominant (B.I.blowupMap ⁻¹ᵁ B.preservedOpen).ι :=
      B.I.isSchemeTheoreticallyDominant_blowupMap_preimage_compl_support
    have : IsSchemeTheoreticallyDominant (B.I.blowupMap ⁻¹ᵁ c.i.opensRange).ι :=
      .preimage_ι_of_le B.I.blowupMap B.le_preservedOpen
        B.I.isIso_blowupMap_restrict_support_compl
    refine (isSchemeTheoreticallyDominant_iff_opensRange_ι (v ≫ Vgr.ι)).mpr ?_
    rwa [opensRange_eq_preimage_of_comp_eq B.I.blowupMap _ hq]
  let σ₀ : CompactifiedProperExtension u O :=
    { V := Vgr.toScheme
      ψ := ψ
      isProper_ψ := hψ
      υ := v
      υ_ψ := hvψ
      isIso_ψ_restrict := hiso
      X :=
        { Z := B.I.blowup
          g := B.I.blowupMap ≫ c.g
          i := Vgr.ι
          comm := hψu
          isProper := inferInstance
          isOpenImmersion := inferInstance }
      isSchemeTheoreticallyDominant_emb := hdense }
  -- Stacks 0F3V: separate the two boundary loci of `σ₀`
  have : IsNoetherian σ₀.X.Z := σ₀.isNoetherian_Z
  have : CompactSpace Vgr.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have : IsNoetherian Vgr.toScheme := ⟨⟩
  have hT₁ : IsClosed (ψ ⁻¹' ((O' : Set U)ᶜ)) :=
    O'.isOpen.isClosed_compl.preimage ψ.continuous
  have hT₂ : IsClosed (ψ ⁻¹' ((O : Set U)ᶜ)) :=
    O.isOpen.isClosed_compl.preimage ψ.continuous
  have hdisj : Disjoint (ψ ⁻¹' ((O' : Set U)ᶜ)) (ψ ⁻¹' ((O : Set U)ᶜ)) := by
    refine Disjoint.preimage _ ?_
    have huniv : (O' : Set U) ∪ (O : Set U) = Set.univ := by
      have := congrArg (fun W : U.Opens ↦ (W : Set U)) hcov
      simpa [Set.union_comm] using this
    rwa [Set.disjoint_iff_inter_eq_empty, ← Set.compl_union, Set.compl_empty_iff]
  obtain ⟨B₁, hB₁⟩ := exists_admissibleBlowup_disjoint_closures
    (TopologicalSpace.NoetherianSpace.isCompact _) hT₁ hT₂
    (TopologicalSpace.NoetherianSpace.isCompact _)
    (TopologicalSpace.NoetherianSpace.isCompact _) hdisj
  -- the separating blow-up is admissible for the open range of the compactification of `σ₀`
  let B₁' : IsAdmissible σ₀.X.Z σ₀.X.i.opensRange :=
    { I := B₁.I
      finiteType := B₁.finiteType
      disjoint_support := by simpa [σ₀] using B₁.disjoint_support }
  refine ⟨σ₀.admissibleBlowup B₁', ?_⟩
  rw [CompactifiedProperExtension.Prepared, σ₀.admissibleBlowup_selfBoundary B₁' O',
    σ₀.admissibleBlowup_forbiddenBoundary]
  exact hB₁

end AlgebraicGeometry
