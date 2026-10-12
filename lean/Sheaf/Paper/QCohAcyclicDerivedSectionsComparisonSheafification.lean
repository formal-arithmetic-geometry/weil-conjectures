/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DerivedSectionPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Sheafification of the full section cohomology presheaf computes the cohomology
sheaf of derived direct image.

Source: Stacks Project, Cohomology, Tag 0D5X (the unbounded higher-direct-image
presheaf description), with Tag 0BKJ (sheafification of cohomology)
(blueprint: new-qcoh-acyclic-sheafification-component).

Proof:
1. Resolve a complex representing E functorially by a K-injective complex I.
   Both right derived functors in the statement are computed on I: the presheaf
   complex is the underlying module presheaf of f_*I, whereas the sheaf complex
   is f_*I. Additive functors preserve homotopy equivalences, so this comparison
   is independent of the resolution and descends to the derived category.
2. The presheaf category computes kernels and cokernels on each open. Thus its
   degree-i cohomology is the quotient of sectionwise cycles by boundaries,
   with exactly the restriction maps in schemeDerivedSectionPresheaf.
3. Module sheafification is exact and its counit on a sheaf is invertible.
   It therefore sends the cycles, boundaries and their quotient in step 2 to
   the cycles, boundaries and cohomology sheaf of f_*I. The latter is
   H^i(Rf_*E), by the K-injective computation of derived direct image.
4. Exact-functor homology comparison and the counit are natural in chain maps.
   Their compatibility with homotopy and quasi-isomorphism gives a natural
   isomorphism on the derived category. Restrict it along the full inclusion
   of objects with quasi-coherent cohomology to obtain the displayed result.
   This argument does not need qcqs or hacyc, but applies under the given hypotheses. -/
theorem qcoh_acyclic_derived_sections_comparison_sheafification {X Y : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hacyc : ∀ (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      F.IsQuasicoherent → ∀ (p : ℤ), 0 < p →
        IsZero ((schemeModuleHigherDirectImage f p).obj F))
    (i : ℤ) :
    Nonempty
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedSectionPresheaf f i ⋙
          PresheafOfModules.sheafification.{u}
            (𝟙 (moduleRings Y.toRingedSpace).obj) ≅
        (schemeDerivedQCohProperty X).ι ⋙ schemeHigherDirectImage f i) := by
  sorry

end AlgebraicGeometry
