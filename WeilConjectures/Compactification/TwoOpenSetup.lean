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

Let `u : U ⟶ S` be separated and of finite type over a Noetherian scheme `S` and let `O`,
`O'` be opens covering `U`. This file constructs a
`AlgebraicGeometry.CompactifiedProperExtension u O` whose two boundary closures are
disjoint, i.e. one prepared side of the two-open compactification theorem
(`AlgebraicGeometry.exists_prepared_compactifiedProperExtension`; blueprint:
`def:nagata-two-open-dense-compactifications` through
`lemma:nagata-two-open-prepared-boundaries`, proof order items 34–36 applied).

The construction: choose a scheme-theoretically dense compactification of `O ⟶ S`
(proof order item 34, `exists_compactification_isSchemeTheoreticallyDominant`), extend it
by the graph construction (Stacks Project Tag 0F3Z,
`Compactification.nonempty_properExtension`; blueprint
`def:nagata-two-open-graph-extensions`, `lemma:nagata-two-open-graph-extensions`,
`def:nagata-two-open-boundary-loci`, `lemma:nagata-boundary-loci`), and separate the two
boundary closures by the constructible-boundary separation blow-up (Stacks Project Tags
080P and 0F3V, `exists_admissibleBlowup_disjoint_closures`), transporting the side along
it with `CompactifiedProperExtension.admissibleBlowup`.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

variable {U S : Scheme.{u}}

/-- **Existence of a prepared side** (blueprint:
`def:nagata-two-open-dense-compactifications` through
`lemma:nagata-two-open-prepared-boundaries`; proof order items 34–36 applied).

Choose a scheme-theoretically dense compactification, extend it to a proper morphism to
`U` by the graph construction (Stacks Project Tag 0F3Z), and separate the two boundary
closures by the boundary-separation blow-up (Stacks Project Tag 0F3V). -/
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
  obtain ⟨B, Vgr, ψ, v, hψ, hv, hvπ, hvψ, hpre, hiso, hψu⟩ :=
    (Compactification.nonempty_properExtension u O
      (TopologicalSpace.NoetherianSpace.isCompact _) c).some
  have := hψ
  have := hv
  have := B.isProper_blowupMap
  -- the embedded copy of `O` is scheme-theoretically dense in the blown-up compactification
  have hdom : IsSchemeTheoreticallyDominant (v ≫ Vgr.ι) := by
    have hq : (v ≫ Vgr.ι) ≫ B.I.blowupMap = c.i := by rw [Category.assoc, hvπ]
    have : IsSchemeTheoreticallyDominant c.i := hc
    have : IsSchemeTheoreticallyDominant c.i.opensRange.ι :=
      (isSchemeTheoreticallyDominant_iff_opensRange_ι c.i).mp hc
    have : IsSchemeTheoreticallyDominant (B.I.blowupMap ⁻¹ᵁ B.preservedOpen).ι :=
      B.I.isSchemeTheoreticallyDominant_blowupMap_preimage_compl_support
    have : IsIso (B.I.blowupMap ∣_ c.i.opensRange) := B.isIso_blowupMap_restrict
    have : IsSchemeTheoreticallyDominant (B.I.blowupMap ⁻¹ᵁ c.i.opensRange).ι :=
      .preimage_ι_of_le B.I.blowupMap B.le_preservedOpen
        B.I.isIso_blowupMap_restrict_support_compl
    refine (isSchemeTheoreticallyDominant_iff_opensRange_ι (v ≫ Vgr.ι)).mpr ?_
    rwa [opensRange_eq_preimage_of_comp_eq B.I.blowupMap _ hq]
  -- the graph-extension side
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
      isSchemeTheoreticallyDominant_emb := hdom }
  -- Stacks 0F3V: separate the two boundary loci of `σ₀`
  have : IsNoetherian σ₀.X.Z := σ₀.isNoetherian_Z
  have : CompactSpace σ₀.V :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have : IsNoetherian σ₀.V := ⟨⟩
  have hT₁ : IsClosed (σ₀.ψ ⁻¹' ((O' : Set U)ᶜ)) :=
    O'.isOpen.isClosed_compl.preimage σ₀.ψ.continuous
  have hT₂ : IsClosed (σ₀.ψ ⁻¹' ((O : Set U)ᶜ)) :=
    O.isOpen.isClosed_compl.preimage σ₀.ψ.continuous
  have huniv : (O' : Set U) ∪ (O : Set U) = Set.univ := by
    have := congrArg (fun W : U.Opens ↦ (W : Set U)) hcov
    simpa [Set.union_comm] using this
  have hdisj : Disjoint (σ₀.ψ ⁻¹' ((O' : Set U)ᶜ)) (σ₀.ψ ⁻¹' ((O : Set U)ᶜ)) := by
    refine Disjoint.preimage _ ?_
    rwa [Set.disjoint_iff_inter_eq_empty, ← Set.compl_union, Set.compl_empty_iff]
  obtain ⟨B₁, hB₁⟩ := exists_admissibleBlowup_disjoint_closures (U := Vgr)
    (TopologicalSpace.NoetherianSpace.isCompact _) hT₁ hT₂
    (TopologicalSpace.NoetherianSpace.isCompact _)
    (TopologicalSpace.NoetherianSpace.isCompact _) hdisj
  -- the ambient open of `σ₀` is the range of its open immersion
  let B₂ : IsAdmissible σ₀.X.Z σ₀.X.i.opensRange :=
    { I := B₁.I
      finiteType := B₁.finiteType
      disjoint_support := by
        have h : σ₀.X.i.opensRange = Vgr := Scheme.Opens.opensRange_ι Vgr
        rw [h]
        exact B₁.disjoint_support }
  refine ⟨σ₀.admissibleBlowup B₂, ?_⟩
  rw [CompactifiedProperExtension.Prepared, σ₀.admissibleBlowup_selfBoundary B₂ O',
    σ₀.admissibleBlowup_forbiddenBoundary]
  exact hB₁

end AlgebraicGeometry
