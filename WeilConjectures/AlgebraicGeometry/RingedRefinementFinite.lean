/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedRefinementConstruction
import WeilConjectures.AlgebraicGeometry.RingedRefinementFiniteRealizationExists
import WeilConjectures.AlgebraicGeometry.RingedRefinementFiniteComparisonExists

/-!
# Finite constant coefficients and the intrinsic strict tower realization

(blueprint: lem-pur-ringed-refinement-finite-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.RingedRefinement

/-- Section-preserving realization identifies the finite refinement with strict towers.
Source: coefficient supplement Step 10; Stacks 00Z4, 03D1, 0H7J, 07A6
(blueprint: lem-pur-ringed-refinement-finite-normalization).
Proof: apply the realization-existence substep, then apply the independent comparison
and normalization substep to its chosen realization.  The two substeps construct the
section-preserving diagram equivalence, all ordinary and derived comparisons, and the
normalized refinement mate.
-/
theorem ringedRefinementFinite {T : Scheme.{u}} (P : Package .systems T)
    (B : Type (u + 1)) [CommRing B] [Finite B] :
    ∃ (e : ∀ W : Over T, FiniteRealization P B W) (k : FiniteComparison P B e),
      FiniteNormalization P B e k := by
  obtain ⟨e⟩ := finiteRealization_exists P B
  obtain ⟨k, hk⟩ := finiteComparison_exists P B e
  exact ⟨e, k, hk⟩

end SheafOfModules.RingedRefinement
