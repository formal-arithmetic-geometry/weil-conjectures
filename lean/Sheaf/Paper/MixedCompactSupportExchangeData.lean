module

public import Sheaf.Paper.RelativeCompactSupportPasting
public import Sheaf.Paper.FiniteCompactSupportEvaluationRefinement
public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.CompleteCompactSupportProetale

/-! # Canonical compact-support exchange and refinement data

Source: the current blueprint's constituent base-change compatibility assembly,
Stacks 07A7, 0E47, 0F7B and 0F7F
(blueprint: def-sf-mixed-compact-support-exchange-data).

This module re-exports the existing ordinary operations and their normalized
exchange and refinement maps, the simultaneous-system proper exchange, the raw
rational scalar-extension functor, and the completed refinement map. Their owning
DAG definition records these constructions separately from the pasting theorems.
`ordinaryExchange` is an abbreviation of the published ordered ordinary exchange.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale.ConstantCompactificationExchange
open AlgebraicGeometry.ProEtale.RelativeCompactSupport

namespace WeilConjectures.MixedCompactSupportData

/-- Re-export the actual ordinary proper mate followed by the open comparison.
The underlying operations, source pullback comparison, ordinary refinement,
whole-system proper exchange, rational scalar extension and completed refinement
are the unchanged public declarations imported above, listed in the node record.
Source: Stacks 07A7, 0E47 and 0F7F; blueprint constituent base-change assembly
(blueprint: def-sf-mixed-compact-support-exchange-data). -/
abbrev ordinaryExchange (B : Type (u + 1)) [CommRing B]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (a : Y' ⟶ Y) (x : X' ⟶ X) (z : c'.Z ⟶ c.Z)
    (sp : IsPullback z c'.g c.g a) (sj : IsPullback x c'.i c.i z) :
    (ordinaryJ B c.i ⋙ ordinaryR B c.g) ⋙ ordinaryG B a ⟶
      ordinaryG B x ⋙ (ordinaryJ B c'.i ⋙ ordinaryR B c'.g) :=
  ordinaryH B c c' a x z sp sj

end WeilConjectures.MixedCompactSupportData
