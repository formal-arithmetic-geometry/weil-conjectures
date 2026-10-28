/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel

/-!
# Compatibility: integral models of constructible `E`-complexes

Blueprint `sk-thm-sfb-rationalization-comparison`
(`ProEtale.isLocalization_boundedConstructibleExtendScalars`), stated in the form used by the
uniform `Ext` bound for `E` (blueprint `det-uniform-constructible-ext-rational`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] [TopologicalSpace.NoetherianSpace X]

/-- Compatibility from blueprint `sk-thm-sfb-rationalization-comparison`: every bounded
constructible `E`-complex is the extension of scalars of a bounded constructible
`𝒪_E`-complex. -/
lemma uniformExtBoundCompat_integralModel (E : FiniteIntermediateField ℓ)
    (K : BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X)) :
    ∃ K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X),
      Nonempty ((boundedConstructibleExtendScalars X ℓ E).obj K₀ ≅ K) :=
  exists_boundedConstructibleExtendScalars_obj_iso X ℓ E K

end AlgebraicGeometry.ProEtale
