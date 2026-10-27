/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E9
-/
module

public import Sheaf.AlgebraicGeometry.VaryingRingOrdinaryEvaluationComparisons

/-!
# Normalization of the ordinary realization comparisons

Source: Zheng, Construction 4.1; Stacks Project, Tags 03DI and 09AE.
(blueprint: lem-sp-varying-ring-ordinary-comparison-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
attribute [local instance 2000] WeilConjectures.SemilinearSections.sequenceSmall
  StrictTower.towers_hasDerivedCategory Scheme.proEtaleRingModules_hasDerivedCategory

/-- The two construction normalizations, before any cartesian or section arrow.
Source: Zheng, Construction 4.1; Stacks 03DI and 09AE
(blueprint: lem-sp-varying-ring-ordinary-comparison-normalization).
Proof: use ordinaryRealization_eq to replace realization by its explicit
component/constant/single composite, keeping the equality transports. Apply
constant embedding and degree-zero embedding to ordinaryModuleEvalG_comp.
Naturality moves each evaluation comparison past its exact-single comparison;
the natural-isomorphism and compositor coherence of the exact-single comparison
identifies the remaining factors. Constant-tower comparison composes termwise.
This gives the specified pullback-composition equation.
For open composition first identify the mate of ordinaryOpenComparison.inv
with ordinaryPullComparison.hom. The defining inverse mate evalJInv of evalG
has this unit equation after localization. The fully faithful degree-zero
embedding recovers its ordinary version, constant embedding makes the unit
termwise, and the exact-single localization factors give the derived strict
unit. Whisker with evaluation and the realization equality isomorphisms.
Transpose the two inverse open-composition maps under the composite open
adjunctions. Mate pasting identifies their mates with the pullback-composition
maps just proved. Conjugation sends moduleJComp.inv and StrictTower.jComp.inv
to the corresponding inverse pullback compositors, by their leftAdjointCompIso
normalization. The pullback equation therefore makes the mates equal.
Injectivity of mateEquiv gives equality of inverse isomorphisms; inversion gives
the displayed forward open-composition equation. Neither calculation uses a
cartesian beta map or a clopen section projection. -/
theorem ordinaryComparisonNormalization (n : ℕ) :
    OrdinaryPullComposition R φ n (ordinaryPullComparison R φ n) ∧
      OrdinaryOpenComposition R φ n (ordinaryOpenComparison R φ n) := by
  sorry

end AlgebraicGeometry.ProEtale.VaryingRing
