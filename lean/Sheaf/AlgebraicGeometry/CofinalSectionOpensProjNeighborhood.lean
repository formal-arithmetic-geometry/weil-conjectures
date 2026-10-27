/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q93
-/
module

public import WeilConjectures.AlgebraicGeometry.AmpleProjCanonicalMap
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.SectionRingLocalizationBijective
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Comparing Proj neighborhoods from mutually refining section opens

Source: Stacks Project, Properties, Tags 01PW and 01PZ, and the chart comparison
supplying Guo Proposition 6.2's translation-extension assertion
(blueprint: lem-sfb-cofinal-section-opens-proj-neighborhood).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- Mutually refining nonvanishing opens give isomorphic neighborhoods of the canonical
images in the two section-ring Proj schemes, over the given affine base.
Source: Stacks Project, Properties, Tags 01PW and 01PZ; the agent-formulated comparison
used in Guo Proposition 6.2
(blueprint: lem-sfb-cofinal-section-opens-proj-neighborhood).

The two canonical morphisms are the witnesses of `exists_sectionRing_proj_morphism`.
Its inverse-image equalities and fraction formula determine the morphisms uniquely:
the fraction formula determines each affine-chart morphism, and the chart preimages
cover the source. Hence the choice here names the canonical morphism, without introducing
an unspecified map. The maps `pL` and `pK` are the induced base structures, expressed
by their defining triangles `hpL` and `hpK`. For a qcqs source the canonical morphisms
identify the target structure sheaves with their direct images, so these triangles
uniquely characterize the induced structures (the base is affine, hence separated).

Proof, following the node's seven steps:
1. Apply `lem-sc-section-ring-localization-bijective` to the canonical fraction formula.
The chart ring maps are isomorphisms; the nonvanishing opens need not be affine.
2. By `lem-weil-pbc-sheaf-morphism-on-basis` the map from each Proj structure sheaf to
the direct image is an isomorphism. Every restriction of the canonical map is therefore
scheme-theoretically dominant.
3. Whenever `Y_s` is contained in `Y_t`, transport restriction of functions through the
two chart ring isomorphisms. By `lem-weil-pbc-morphism-into-affine-scheme` this gives
`D_L(s) → D_K(t)`, commuting with the source maps and the maps to the affine base.
4. The first refinement and the section cover give a union of source charts containing
the first canonical image. On overlaps the chart morphisms agree after the canonical
map. Use `lemma-nagata-ext-scheme-theoretically-dominant-separated`, with the absolute
separatedness from `lem-trf-proj-separated`, and `lem-weil-pbc-scheme-morphism-gluing`
to obtain a morphism from that neighborhood to the second Proj.
5. Interchange the two modules, using the second refinement, to construct the reverse map.
6. Intersect each neighborhood with the inverse image of the other. The composites agree
with the ambient inclusions after the canonical maps. Scheme-theoretic dominance and
separated-target uniqueness make these equalities hold on the neighborhoods themselves.
7. These identities show that the two maps corestrict to the chosen opens and are inverse.
Their construction preserves the base maps and their composites with the source maps.
The factorization equalities below express containment of the canonical images. -/
theorem exists_cofinal_section_opens_proj_neighborhood_iso
    (B Y : Scheme.{u}) [IsAffine B] (q : Y ⟶ B)
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (L K : Y.Modules) [L.IsInvertible] [K.IsInvertible]
    (hL : ∀ y : Y, ∃ (d : ℕ) (s : sectionRingGrade L d),
      0 < d ∧ y ∈ nonvanishingLocus (L.tensorPow d) (s.val d))
    (hK : ∀ y : Y, ∃ (n : ℕ) (t : sectionRingGrade K n),
      0 < n ∧ y ∈ nonvanishingLocus (K.tensorPow n) (t.val n))
    (hLK : ∀ (n : ℕ), 0 < n → ∀ (t : sectionRingGrade K n) (y : Y),
      y ∈ nonvanishingLocus (K.tensorPow n) (t.val n) →
        ∃ (d : ℕ) (s : sectionRingGrade L d), 0 < d ∧
          y ∈ nonvanishingLocus (L.tensorPow d) (s.val d) ∧
          nonvanishingLocus (L.tensorPow d) (s.val d) ⊆
            nonvanishingLocus (K.tensorPow n) (t.val n))
    (hKL : ∀ (d : ℕ), 0 < d → ∀ (s : sectionRingGrade L d) (y : Y),
      y ∈ nonvanishingLocus (L.tensorPow d) (s.val d) →
        ∃ (n : ℕ) (t : sectionRingGrade K n), 0 < n ∧
          y ∈ nonvanishingLocus (K.tensorPow n) (t.val n) ∧
          nonvanishingLocus (K.tensorPow n) (t.val n) ⊆
            nonvanishingLocus (L.tensorPow d) (s.val d))
    (pL : Proj (sectionRingGrade L) ⟶ B)
    (pK : Proj (sectionRingGrade K) ⟶ B)
    (hpL : (exists_sectionRing_proj_morphism Y L hL).choose ≫ pL = q)
    (hpK : (exists_sectionRing_proj_morphism Y K hK).choose ≫ pK = q) :
    ∃ (VL : (Proj (sectionRingGrade L)).Opens)
      (VK : (Proj (sectionRingGrade K)).Opens)
      (rL : Y ⟶ VL.toScheme) (rK : Y ⟶ VK.toScheme)
      (θ : VL.toScheme ≅ VK.toScheme),
      rL ≫ VL.ι = (exists_sectionRing_proj_morphism Y L hL).choose ∧
      rK ≫ VK.ι = (exists_sectionRing_proj_morphism Y K hK).choose ∧
      rL ≫ θ.hom = rK ∧
      θ.hom ≫ VK.ι ≫ pK = VL.ι ≫ pL := by
  sorry

end AlgebraicGeometry.Scheme.Modules
