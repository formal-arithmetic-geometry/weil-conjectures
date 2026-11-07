/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.WeilSheaf.VerdierExchange
public import Submission.WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Functor.FullyFaithful

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The Verdier exchange for Weil complexes (re-export)

This module re-exports `WeilConjectures.WeilSheaf.VerdierExchange`, which contains the statements
formerly duplicated here (`WeilConjectures.CoefficientClosedStructure.curryYonedaIso`,
`AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedTensorCurryYonedaIso`,
`AlgebraicGeometry.WeilComplex.nativeConstructibleTensorCurryYonedaIso`,
`AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_op_comp_iso_of_adjunction`); the copies
were removed because a module importing both saw every declaration twice (lean-eval bump dedup,
2026-11-07).
-/
