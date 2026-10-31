/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingedRefinementFiniteRealizationExists
/-! Finite operation comparisons and normalization.
(blueprint: new-lem-pur-ringed-refinement-finite-comparison-exists).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization
namespace SheafOfModules.RingedRefinement
/-- A chosen finite realization admits all normalized operation comparisons.
Source: coefficient supplement Step 10; Stacks 03D1, 03D7, 03DI, 07A6 and 0B65.
The proof transports the sectionwise direct-image comparison across the equivalence,
descends it to ordinary derived localization, and obtains the proper/open refinement
equation by normalized mate calculation.
(blueprint: new-lem-pur-ringed-refinement-finite-comparison-exists).
-/
theorem finiteComparison_exists {T : Scheme.{u}} (P : Package .systems T)
    (B : Type (u + 1)) [CommRing B] [Finite B]
    (e : ∀ W : Over T, FiniteRealization P B W) :
    ∃ k : FiniteComparison P B e, FiniteNormalization P B e k := by
  sorry
end SheafOfModules.RingedRefinement
