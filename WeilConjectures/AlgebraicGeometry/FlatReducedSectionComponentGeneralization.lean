/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Inseparable

import WeilConjectures.AlgebraicGeometry.FlatPointedNoetherianComponentModel
import WeilConjectures.AlgebraicGeometry.FlatReducedSpecializationTraitData
import WeilConjectures.AlgebraicGeometry.FlatTraitTwoSectionConnectedOpen

/-!
# Generalization stability of a section component in a flat geometrically reduced family

Source: Stacks Project, More on Morphisms, Tag 055Q,
`lemma-connected-along-section-open-neighbourhood`, its specialization argument.
(blueprint: lem-trf-flat-reduced-section-component-generalization)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Topology IsLocalRing

namespace AlgebraicGeometry

/-- The fibrewise connected components through a section form a locus stable under
 generalization for a flat morphism of finite presentation with geometrically reduced fibres.
The topological fibre in the conclusion is the scheme-theoretic fibre through `g.fiberHomeo`.

Source: Stacks Project, Tag 055Q, `lemma-connected-along-section-open-neighbourhood`.

Proof:
1. Use `exists_flat_pointed_noetherian_component_model` at the specialized point q.
   Lift both points to the open base change. Its first projection is an open immersion,
   so it reflects their specialization. The model's component inverse-image identity
   transfers membership of q. Cartesianness identifies its distinguished reduced
   geometric fibre with the fibre over the image of q. Equal model images settle the claim.
2. Otherwise apply `exists_flat_reduced_specialization_trait_data` to the strict model
   specialization. It supplies a flat finitely presented trait family, a reduced closed
   fibre, two sections meeting the same closed component, and the component inverse-image
   identity for the projection to the model.
3. The generic-component conclusion of `exists_connected_open_two_sections_of_flat_trait`
   puts the graph section's generic point in the component through the original section.
   The graph section equation identifies its image in the base with the generic point.
4. Evaluate the trait component inverse-image identity at that generic section point,
   then the model component inverse-image identity at the lifted original general point.
   These return the required membership in the original family.

(blueprint: lem-trf-flat-reduced-section-component-generalization) -/
theorem stableUnderGeneralization_section_component_of_flat_of_geometricallyReduced_fibers
    {P T : Scheme.{u}} (g : P ⟶ T) [Flat g] [LocallyOfFinitePresentation g]
    [QuasiCompact g] [QuasiSeparated g] (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T)
    (hred : ∀ t : T, GeometricallyReduced (g.fiberToSpecResidueField t)) :
    StableUnderGeneralization
      {p : P | p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))} := by
  intro q p hpq hq
  obtain ⟨V, hqV, P₀, T₀, g₀, σ₀, b, ρ, _, hP₀, hT₀, _,
    hg₀, hfp₀, hqc₀, hqs₀, H, hσ₀, _, hred₀, hcomp⟩ :=
    exists_flat_pointed_noetherian_component_model g σ hσ q (hred (g q))
  let : IsNoetherian P₀ := hP₀
  let : IsNoetherian T₀ := hT₀
  let : Flat g₀ := hg₀
  let : LocallyOfFinitePresentation g₀ := hfp₀
  let : QuasiCompact g₀ := hqc₀
  let : QuasiSeparated g₀ := hqs₀
  have hpV : g p ∈ V := (hpq.map g.continuous).mem_open V.isOpen hqV
  have hqrange : q ∈ Set.range (pullback.fst g V.ι) := by
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    exact hqV
  have hprange : p ∈ Set.range (pullback.fst g V.ι) := by
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    exact hpV
  obtain ⟨qV, hqproj⟩ := hqrange
  obtain ⟨pV, hpproj⟩ := hprange
  have hpqV : pV ⤳ qV :=
    (pullback.fst g V.ι).isOpenEmbedding.isInducing.specializes_iff.mp
      (by simpa only [hpproj, hqproj] using hpq)
  have hq₀ : ρ qV ∈ connectedComponentIn
      (g₀ ⁻¹' {g₀ (ρ qV)}) (σ₀ (g₀ (ρ qV))) := by
    have h := (Set.ext_iff.mp hcomp qV).mpr
      (by simpa only [Set.mem_preimage, Set.mem_ofPred_eq, hqproj] using hq)
    exact h
  have hqbase : pullback.snd g V.ι qV = ⟨g q, hqV⟩ := by
    apply Subtype.ext
    change V.ι (pullback.snd g V.ι qV) = g q
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hqproj]
  have hbase : g₀ (ρ qV) = b ⟨g q, hqV⟩ := by
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply, hqbase]
  have hp₀ : ρ pV ∈ connectedComponentIn
      (g₀ ⁻¹' {g₀ (ρ pV)}) (σ₀ (g₀ (ρ pV))) := by
    by_cases heq : ρ pV = ρ qV
    · simpa only [heq] using hq₀
    obtain ⟨R, hR, hdom, hdvr, a, _, _, hflat, hfp, hqc, hqs, _, _, _, _, _,
      hred, σR, τ, hσR, hτ, _, _, hη, _, htraitcomp, hclosed⟩ :=
      exists_flat_reduced_specialization_trait_data g₀ σ₀ hσ₀
        (hpqV.map ρ.continuous) heq hq₀ (hbase.symm ▸ hred₀)
    let : Flat (pullback.snd g₀ (a ≫ g₀)) := hflat
    let : LocallyOfFinitePresentation (pullback.snd g₀ (a ≫ g₀)) := hfp
    let : QuasiCompact (pullback.snd g₀ (a ≫ g₀)) := hqc
    let : QuasiSeparated (pullback.snd g₀ (a ≫ g₀)) := hqs
    let : IsReduced ((pullback.snd g₀ (a ≫ g₀)).fiber (closedPoint R)) := hred
    have hgeneric := (exists_connected_open_two_sections_of_flat_trait
      (pullback.snd g₀ (a ≫ g₀)) σR τ hσR hτ hclosed).2
    let η : Spec (.of R) := ⟨⊥, Ideal.isPrime_bot⟩
    have hτη : pullback.snd g₀ (a ≫ g₀) (τ η) = η := by
      rw [← Scheme.Hom.comp_apply, hτ]
      rfl
    have hmem : τ η ∈ {x : ↥(pullback g₀ (a ≫ g₀)) |
        x ∈ connectedComponentIn
          ((pullback.snd g₀ (a ≫ g₀)) ⁻¹' {pullback.snd g₀ (a ≫ g₀) x})
          (σR (pullback.snd g₀ (a ≫ g₀) x))} := by
      simpa only [Set.mem_ofPred_eq, hτη] using hgeneric
    have h := (Set.ext_iff.mp htraitcomp (τ η)).mp hmem
    simpa only [Set.mem_preimage, Set.mem_ofPred_eq, η, hη] using h
  have h := (Set.ext_iff.mp hcomp pV).mp hp₀
  simpa only [Set.mem_preimage, Set.mem_ofPred_eq, hpproj] using h

end AlgebraicGeometry
