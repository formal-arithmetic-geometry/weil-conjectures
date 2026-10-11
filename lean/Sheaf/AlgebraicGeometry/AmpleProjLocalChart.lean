/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.InvertibleSectionRing
public import Sheaf.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Affine charts of the canonical section-ring morphism

Source: Stacks Project, Properties, Tags 01PZ and 01Q1, with the chart formula of
Constructions Tag 01N8 (blueprint: lem-sc-ample-proj-local-chart).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical section-ring morphism identifies any affine nonvanishing chart when `L`
is ample. Here `X_s` is `nonvanishingLocus (L.tensorPow d) (s.val d)`.
Source: Stacks Project, Properties, Tags 01PZ and 01Q1
(blueprint: lem-sc-ample-proj-local-chart).

Step 1: `lem-sc-ample-proj-canonical-map` supplies the morphism from the assumed cover,
its inverse-image identity, and its localized sections formula (that statement writes
`X_s` as the generating locus, which equals the nonvanishing locus for an invertible
module). The formula below specifies the canonical map: the pullback of `ξ / s^n`,
multiplied by the restricted section `s^n`, is the restricted numerator. Since `s`
generates on its nonvanishing open, this determines the pullback of every fraction,
including on the empty open.

Step 2: ampleness gives quasi-compactness by `def-weil-pbc-ample-invertible-module` and
separatedness, hence quasi-separatedness, by `lem-weil-pbc-ample-scheme-separated`.

Step 3: for a section of degree `d > 0`, apply `lem-sc-invert-s-cohomology` in degree
zero to the invertible module `L^{⊗ d}` and the structure sheaf. It identifies the
localized Veronese section ring with the functions on `X_s`. Reindexing degrees
identifies that degree-zero localization with `S_(s)`.

Step 4: by `def-pc-proj`, the chart is `Spec S_(s)`. The localization formula from
Step 1 identifies its induced functions map with the isomorphism of Step 3.

Step 5: `lem-sc-affine-global-sections-iso` makes the chart morphism an isomorphism,
since its source and target are affine and its functions map is an isomorphism.
The source of `f ∣_ D₊(s)` is the inverse image of the chart, identified with `X_s`
by the first equality; thus this is precisely the induced morphism in the node. -/
theorem exists_sectionRing_proj_affine_charts (X : Scheme.{u}) (L : X.Modules)
    [L.IsInvertible]
    (hcover : ∀ x : X, ∃ (d : ℕ) (s : sectionRingGrade L d),
      0 < d ∧ x ∈ nonvanishingLocus (L.tensorPow d) (s.val d)) :
    ∃ f : X ⟶ Proj (sectionRingGrade L),
      ∀ (d : ℕ) (_hd : 0 < d) (s : sectionRingGrade L d),
        (f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val : Set X) =
          nonvanishingLocus (L.tensorPow d) (s.val d) ∧
        (∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
          (f.app (Proj.basicOpen (sectionRingGrade L) s.val)
            (Proj.awayToSection (sectionRingGrade L) s.val
              (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
                ξ.val ξ.property))) •
            (L.tensorPow (n • d)).presheaf.map (homOfLE
              (le_top : f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val ≤ ⊤)).op
              ((s.val ^ n) (n • d)) =
          (L.tensorPow (n • d)).presheaf.map (homOfLE
              (le_top : f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val ≤ ⊤)).op
            (ξ.val (n • d))) ∧
        (IsAmple X L → ∀ U : X.Opens,
          (U : Set X) = nonvanishingLocus (L.tensorPow d) (s.val d) → IsAffineOpen U →
          IsIso (f ∣_ Proj.basicOpen (sectionRingGrade L) s.val)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
