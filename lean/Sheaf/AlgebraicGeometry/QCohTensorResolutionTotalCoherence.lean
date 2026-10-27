/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTotalCoherence
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionRestrictionCoherence
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionTotalComponents

/-! # Total tensor comparisons under successive affine restrictions

Compatibility import for `AlgebraicGeometry.tensorResolutionChartRestrictionComplexIso`,
`AlgebraicGeometry.tensorResolutionChartRestriction_total_inv`, and
`AlgebraicGeometry.tensorResolutionChartRestriction_total`.

The source module supplies the componentwise restriction isomorphism and the same two proved
coherence identities. Re-exporting it avoids mixing the Sheaf and source copies of their
common tensor-naturality dependencies. The explicit Sheaf dependency paths re-export the
same canonical declarations and remain compatible with this module.
-/

@[expose] public section
