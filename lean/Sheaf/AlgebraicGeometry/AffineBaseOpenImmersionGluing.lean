module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Topology.Defs.Filter
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# Gluing open immersions over an affine open cover of the base

Source: Stacks Project, Tag 01SM, `lemma-characterize-quasi-affine`, the final
local-to-global assertion in the proof of (2) implies (4)
(blueprint: lem-a1-affine-base-open-immersion-gluing).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Compatible open immersions above an affine open cover glue to a unique morphism,
which is a quasi-compact open immersion over the base.

Source: Stacks Project, Tag 01SM, `lemma-characterize-quasi-affine`, proof of (2)
implies (4) (blueprint: lem-a1-affine-base-open-immersion-gluing).

Proof plan:
1. The inverse images of the base opens cover `Z`. Apply scheme morphism gluing
   (`lem-weil-pbc-scheme-morphism-gluing`) to `e a` followed by the inclusion into `Y`.
   The overlap hypothesis gives compatibility; the same gluing lemma gives uniqueness.
2. The equations over each base open imply `c ≫ π = h`, checked on that cover.
   Thus the inverse image under `c` of `π ⁻¹ᵁ U a` is `h ⁻¹ᵁ U a`, and its
   restriction is `e a`.
3. If two points have equal image in `Y`, choose a base chart containing its image
   in `S`. Both points lie in that source chart, where `e a` is injective.
   Each source-chart composite into `Y` is an open immersion. Apply
   `lem-weil-pbc-open-immersion-injective-local-source` to conclude globally.
4. Since `π` is affine, each target chart is affine and hence quasi-separated by
   `lem-weil-pbc-affine-scheme-qcqs`. Its source chart is quasi-compact, so
   `lem-weil-pbc-qcqs-morphism-permanence` makes `e a` quasi-compact.
5. The target charts cover `Y`; `lem-pc-quasi-compact-local-on-target` now makes
   `c` quasi-compact. For an empty index type the cover forces `S`, `Z` and `Y`
   empty, and all the same arguments apply. -/
theorem exists_unique_quasiCompact_isOpenImmersion_of_affine_base_cover
    {Z Y S : Scheme.{u}} (h : Z ⟶ S) (π : Y ⟶ S) [IsAffineHom π]
    {A : Type v} (U : A → S.Opens) (hU : iSup U = ⊤)
    (hUa : ∀ a : A, IsAffineOpen (U a))
    (hZ : ∀ a : A, CompactSpace (h ⁻¹ᵁ U a).toScheme)
    (e : ∀ a : A, (h ⁻¹ᵁ U a).toScheme ⟶ (π ⁻¹ᵁ U a).toScheme)
    (he : ∀ a : A, IsOpenImmersion (e a))
    (heS : ∀ a : A, e a ≫ (π ∣_ U a) = h ∣_ U a)
    (heq : ∀ a b : A,
      Z.homOfLE (inf_le_left : h ⁻¹ᵁ U a ⊓ h ⁻¹ᵁ U b ≤ h ⁻¹ᵁ U a) ≫
          e a ≫ (π ⁻¹ᵁ U a).ι =
        Z.homOfLE (inf_le_right : h ⁻¹ᵁ U a ⊓ h ⁻¹ᵁ U b ≤ h ⁻¹ᵁ U b) ≫
          e b ≫ (π ⁻¹ᵁ U b).ι) :
    ∃ c : Z ⟶ Y,
      (∀ a : A, (h ⁻¹ᵁ U a).ι ≫ c = e a ≫ (π ⁻¹ᵁ U a).ι) ∧
      c ≫ π = h ∧ QuasiCompact c ∧ IsOpenImmersion c ∧
      ∀ c' : Z ⟶ Y,
        (∀ a : A, (h ⁻¹ᵁ U a).ι ≫ c' = e a ≫ (π ⁻¹ᵁ U a).ι) → c' = c := by
  sorry

end AlgebraicGeometry
