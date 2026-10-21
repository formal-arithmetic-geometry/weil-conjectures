/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.CompletedFiniteComparisonModels

/-!
# Existence of normalized finite completed-ring comparisons

Source: Stacks 099N, 03DI and 06XN; finite-exchange proof Step 7
(blueprint: lem-cbc-normalized-finite-comparison-existence).

The source and target comparisons are specified by their counit equations on
K-flat representatives. Uniqueness is proved separately in the parent module.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

variable {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : OpenImmersionSquare gU j' j g)

open AlgebraicGeometry.ProEtale.StrictTower

/-- Existence of the normalized finite source and target comparisons.
Source: Stacks 099N, 03DI, 06XN; finite-exchange proof Step 7
(blueprint: lem-cbc-normalized-finite-comparison-existence).
Proof: choose a flat-term K-flat representative P. Finite scalar extension is computed
by ordinary tensor on P. Exact open extension commutes with reduction by the map
[p] tensor b to [p tensor b restricted to the open], including strict transitions.
The normalized finite-evaluation comparison for completed pullback therefore computes
both endpoints on P. Its ordinary finite coordinate change is cbcSourceLevel or
cbcTargetLevel, respectively: the coefficient comparison preserves constant sections,
the open comparison preserves extension summands, and the pullback scalar mate sends
b tensor m to pi_n(b) tensor m. These formulas identify the universal counits with the
displayed representative model maps. They are isomorphisms on this resolving class.
Compose the first model comparison with the inverse finite model comparison and use
naturality on chain maps between resolutions. K-flat resolutions exist for every
complex, and both derived endpoints invert quasi-isomorphisms, so resolving-class
descent produces the two natural isomorphisms, with the required normalization.
This assertion supplies existence only; uniqueness follows separately by cancellation
of the invertible finite model maps and resolution descent. -/
theorem cbcNormalizedFiniteComparison_exists (n : ℕ) :
    (∃ e : completedReductionTower U d ⋙ cbcStrictOpen d j sq.isOpenImmersion ⋙
          completedTowerPullback g d ⋙ pbcTowerEvaluation X' (pbcAdicCompletion X' d) n ≅
        cbcFiniteReduction d U n ⋙ (cbcFiniteSource d sq n).mapDerivedCategory,
      CbcSourceFiniteNormalization d sq n e) ∧
    (∃ e : completedReductionTower U d ⋙ completedTowerPullback gU d ⋙
          cbcStrictOpen d j' sq.isOpenImmersion' ⋙
            pbcTowerEvaluation X' (pbcAdicCompletion X' d) n ≅
        cbcFiniteReduction d U n ⋙ (cbcFiniteTarget d sq n).mapDerivedCategory,
      CbcTargetFiniteNormalization d sq n e) := by
  sorry

end AlgebraicGeometry.Scheme
