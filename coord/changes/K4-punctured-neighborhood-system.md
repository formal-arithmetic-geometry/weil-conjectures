# TopCat.puncturedNeighborhood_coefficient_presentation

## Reason

The general spectral-limit continuity theorem requires sheaves on its stages and their
unit-compatible inverse-image diagram. The punctured-neighborhood theorem is stated
using ambient object cohomology. The restriction coefficient system and the comparisons
of these canonical maps are a separate part of the argument. The topological-system
construction and its limit properties are proved in the same delivery.

## Old

The two new modules and all declarations in them were absent. The assigned module had
one hole in `TopCat.puncturedNeighborhood_cohomology_eventual_zero`.

## New

The assigned declaration's complete signature and original docstring are unchanged.
It now imports, privately, the coefficient-presentation module, general spectral-limit
eventual-zero theorem, and proves its conclusion
from them. The new module `Sheaf.Topology.PuncturedNeighborhoodSpectralSystem` constructs
`puncturedNeighborhoodIndex`, `puncturedNeighborhoodSpace`,
`puncturedNeighborhoodTransition`, `puncturedNeighborhoodProjection` and proves the
nonempty, directed, spectral-stage, spectral-transition and topological-limit properties,
and spectrality of the limit using a private spectral directed-limit import.
`Sheaf.Topology.PuncturedNeighborhoodCoefficientPresentation` states the new theorem
`puncturedNeighborhood_coefficient_presentation`, asserting `Nonempty` of the new
`PuncturedNeighborhoodCoefficients` structure; its full signature is in that module
and verbatim in its node's lean.statement. It identifies the coefficients and maps only;
it makes no assertion of eventual zero detection or class lifting.

No existing public signature, definition, instance, attribute or public import changes.
No source-library file changes. The new theorem is eliminated only inside the assigned
proposition proof, and none of the constructed data definitions depends on it.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Topology.PuncturedNeighborhoodCohomologyEventualZero | K4 | Complete proof from the new presentation and the general continuity theorem. |
| Sheaf.Topology.PuncturedNeighborhoodCohomologyColimit | unclaimed at source inspection | Existing call to the assigned theorem is unchanged; no adaptation. |
| Sheaf.Topology.PuncturedNeighborhoodCoefficientPresentation | new in this delivery | Uses the concrete topological-system definitions in its signature. |

The new declarations have no preexisting users. All other downstream modules retain
the same interface. In particular no target meaning changes and no target statement
review is reopened.

## Status

landed 20261025T123233-L-1845227 2026-10-25 (merge of deliver/K4/Sheaf.Topology.PuncturedNeighborhoodCohomologyEventualZero)
