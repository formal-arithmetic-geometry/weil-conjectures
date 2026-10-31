/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ClopenComparisonTensorSquareData
import WeilConjectures.SixFunctors.ClopenComparisonTensorSquareDataExistence
import WeilConjectures.SixFunctors.ClopenComparisonTensorSquareEquations

/-!
# Tensor squares for open base change and the clopen comparison

Source: Stacks Project, Tags 0F7B, 07A4 and 0GL1; normalized clopen tensor refinement
(blueprint: lem-sf-clopen-comparison-tensor-square).

The existing data module fixes the actual ringed-site operations, their representative
normalizations, the clopen projection and all four equations. Both ordinary and vertical
sequence sites use their ordinary unbounded derived categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.ClopenComparisonTensorSquare

/-- The normalized clopen comparison commutes with derived tensor in both site modes.
The first conclusion supplies simultaneous normalized data; the second asserts the
Cartesian, clopen, composite-open and full comparison equations for every such datum.
No condition is imposed on the derived objects or on coefficient transitions.

Source: Stacks Project, Tags 0F7B, 07A4 and 0GL1; the clopen tensor refinement
(blueprint: lem-sf-clopen-comparison-tensor-square).

Proof plan: use `lem-sf-clopen-comparison-tensor-data-existence` to construct the
simultaneous normalized data. Apply `lem-sf-clopen-comparison-tensor-square-equations`
to every such datum and pair the conclusions. In that equations lemma, restriction to
the open identifies the Cartesian square with the canonical tensor/pullback composite.
The reverse clopen adjunction gives the component projection `(1,0)`, so its tensor
square holds on each of the two open components. The composite-open adjunction fixes
the tensor comparison for `k`. Paste the Cartesian, clopen and composite-open squares,
using naturality and the specified pullback compositors, to obtain the full alpha
square. All steps occur in the derived category of the ringed site itself, including
sequence sites, and do not use a proper projection isomorphism or evaluation faithfulness. -/
theorem clopenComparisonTensorSquare (m : Mode) {A B C D : Scheme.{u}}
    (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (R : Sheaf (topology m D) CommRingCat.{u + 1})
    (S : Sheaf (topology m B) CommRingCat.{u + 1})
    (c : R ⟶ ((baseChange m p).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology m D) (topology m B)).obj S)
    (t : SiteSquare (input m p i R S c))
    (o : Operations (input m p i R S c) t) (a : Assertion o) :
    Nonempty (Data o (AlgebraicGeometry.ProEtale.StrictTower.squareLift k r p i h)) ∧
      ∀ v : Data o (AlgebraicGeometry.ProEtale.StrictTower.squareLift k r p i h),
        Equations a v := by
  constructor
  · exact data_nonempty m k i r p h R S c t o a
  · intro v
    exact equations_for_data a v

end SheafOfModules.ClopenComparisonTensorSquare
