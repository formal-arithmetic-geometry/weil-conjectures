# CategoryTheory.hypercohomologyCouple

## Reason

The definition previously used `sorry` for the exact-couple structure even though
`hypercohomology_maps_exact` already supplies every required field. The body is
replaced by the direct structure construction from those six clauses.

## Old

`noncomputable def hypercohomologyCouple : BigradedExactCouple B 0 := by
  sorry`

## New

`noncomputable def hypercohomologyCouple : BigradedExactCouple B 0 := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hypercohomology_maps_exact F K
  exact { D := hypercohomologyD F K, E := hypercohomologyE F K,
    alpha := hypercohomologyAlpha F K, f := hypercohomologyBoundary F K,
    g := hypercohomologyG F K, alpha_f_zero := h₁, f_g_zero := h₂,
    g_alpha_zero := h₃, exact_alpha := h₄, exact_f := h₅, exact_g := h₆ }`

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.TruncationsAndHomotopyColimits | unclaimed | definition remains definitionally the same exact-couple data |
| Sheaf.AlgebraicGeometry.HypercohomologyConvergence | unclaimed | consumes the same `BigradedExactCouple` interface |
| Sheaf.AlgebraicGeometry.BoundedBelowTruncationCriterion | unclaimed | consumes the same `BigradedExactCouple` interface |
| Sheaf.Paper.ExactCoupleDifferential | unclaimed | consumes the same `BigradedExactCouple` interface |

## Status

landed 20261017T163409-L-3002742 2026-10-17 (merge of deliver/C4/Sheaf.AlgebraicGeometry.HypercohomologyFiltrations)
