/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.SectionComponentPullback
import WeilConjectures.AlgebraicGeometry.SectionNoetherianDescent

/-!
# Local noetherian models for the component selected by a section

## References

* [Stacks Project, Tag 055P](https://stacks.math.columbia.edu/tag/055P)
* [Stacks Project, Tag 055M](https://stacks.math.columbia.edu/tag/055M)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- Near each source point, the section component is the inverse image of the section
component of a finitely presented morphism between noetherian schemes. -/
theorem exists_section_component_noetherian_model {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) (p : P) :
    ∃ (U : P.Opens), p ∈ U ∧ ∃ (P₀ T₀ : Scheme.{u}) (g₀ : P₀ ⟶ T₀)
      (σ₀ : T₀ ⟶ P₀) (ρ : U.toScheme ⟶ P₀),
      IsNoetherian P₀ ∧ IsNoetherian T₀ ∧ LocallyOfFinitePresentation g₀ ∧
      QuasiCompact g₀ ∧ QuasiSeparated g₀ ∧ σ₀ ≫ g₀ = 𝟙 T₀ ∧
      U.ι ⁻¹' {q : P | q ∈ connectedComponentIn (g ⁻¹' {g q}) (σ (g q))} =
        ρ ⁻¹' {q : P₀ | q ∈ connectedComponentIn (g₀ ⁻¹' {g₀ q}) (σ₀ (g₀ q))} := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, _⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g p)) isOpen_univ
  let V : T.Opens := V
  let : IsAffine V.toScheme := hV
  let U := g ⁻¹ᵁ V
  let f := g ∣_ V
  have H : IsPullback U.ι f g V.ι := (isPullback_morphismRestrict g V).flip
  let σV : V.toScheme ⟶ U.toScheme := H.lift (V.ι ≫ σ) (𝟙 V.toScheme) (by
    simp [hσ])
  have hσV : σV ≫ f = 𝟙 V.toScheme := H.lift_snd _ _ _
  have hcompat : σV ≫ U.ι = V.ι ≫ σ := H.lift_fst _ _ _
  obtain ⟨P₀, T₀, g₀, σ₀, ρ, b, hP₀, hT₀, hg₀, hqc₀, hqs₀, hσ₀, H₀, hcompat₀⟩ :=
    exists_noetherian_model_with_section f σV hσV
  let : LocallyOfFinitePresentation g₀ := hg₀
  refine ⟨U, hpV, P₀, T₀, g₀, σ₀, ρ, hP₀, hT₀, hg₀, hqc₀, hqs₀, hσ₀, ?_⟩
  exact (section_component_preimage_of_isPullback g σ hσ U.ι f V.ι H σV hσV hcompat).trans
    (section_component_preimage_of_isPullback g₀ σ₀ hσ₀ ρ f b H₀ σV hσV hcompat₀).symm

end AlgebraicGeometry
