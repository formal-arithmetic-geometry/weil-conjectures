/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices

import WeilConjectures.AlgebraicGeometry.SectionAcyclicIncomingKernelImage
import WeilConjectures.AlgebraicGeometry.ShortComplexSectionComparison

/-! # The section class comparison for acyclic complexes

Source: Stacks Project, Tags 015J and 01E4.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical section-class map commutes homology with sections when both the
terms and the homology sheaves of a nonnegative complex are section-acyclic.
Source: Stacks Project, Tags 015J and 01E4. -/
theorem sectionCohomologyTheta_isIso_of_acyclic
    {Y : Scheme.{u}} (K : CochainComplex Y.Modules ℕ) (V : Y.Opens)
    (hterms : ∀ (n r : ℕ), 0 < r →
      IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj
        ((restrictFunctor V.ι).obj (K.X n))))
    (hhomology : ∀ (n r : ℕ), 0 < r →
      IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj
        ((restrictFunctor V.ι).obj (K.homology n)))) (p : ℕ) :
    IsIso (((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
      (sectionCohomologyTheta K p)).app (op V)) := by
  obtain ⟨hkernel, himage⟩ :=
    section_acyclic_incoming_kernel_image K V hterms hhomology p 1 (by decide)
  exact shortComplex_sectionComparison_isIso (K.sc p) V hkernel himage

end AlgebraicGeometry.Scheme.Modules
