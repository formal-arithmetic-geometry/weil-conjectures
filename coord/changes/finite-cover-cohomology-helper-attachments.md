# Finite-cover cohomology helper attachments

## Reason

The assigned theorem assumes finite-index composition and base change. The two
existing helper declarations instead assume unrestricted indexed composition and
base change. Their DAG statements already concern the finite-cover sites of
Situation 0A34. The unrestricted instances do not follow from the finite ones:
an arbitrary indexed family may repeat one covering arrow infinitely often and
choose different further covers or pullback objects for each repetition.

Attach the existing mathematical nodes to new finite-index helper declarations.
This introduces no duplicate nodes and makes the declared hypotheses agree with
the finite-index colimit-site statement. The old proved declarations and their
modules remain verbatim; consumers can continue to use those special cases.
Neither a target statement nor a definition is changed.

## Old

`lem-weil-pbc-colimit-sites-class-descent`:
`Sheaf.CategoryTheory.CohomologyColimitSitesClassDescent`,
`CategoryTheory.cohomology_colimit_sites_class_descent`.

`lem-weil-pbc-colimit-sites-eventual-vanishing`:
`Sheaf.CategoryTheory.CohomologyColimitSitesEventualVanishing`,
`CategoryTheory.cohomology_colimit_sites_eventual_vanishing`.

Both have `[∀ j, (P j).IsStableUnderComposition]`,
`[∀ j, (P j).IsStableUnderBaseChange]`, `[Q.IsStableUnderComposition]`,
and `[Q.IsStableUnderBaseChange]`.

## New

`lem-weil-pbc-colimit-sites-class-descent`:
`Sheaf.CategoryTheory.CohomologyColimitFiniteCoverSitesClassDescent`,
`CategoryTheory.cohomology_colimit_finite_cover_sites_class_descent`.

`lem-weil-pbc-colimit-sites-eventual-vanishing`:
`Sheaf.CategoryTheory.CohomologyColimitFiniteCoverSitesEventualVanishing`,
`CategoryTheory.cohomology_colimit_finite_cover_sites_eventual_vanishing`.

The four instances use `IsStableUnderFiniteComposition` and
`IsStableUnderFiniteBaseChange`. All other hypotheses and the respective
class-lifting and eventual-zero conclusions match the old signatures. Each new
helper is one whole public theorem hole with the source argument in its docstring.
The DAG statements are unchanged, and the proof plans explain the finite-index
version. The existing helper proof-dependency nodes are retained as the source's
plan; their Lean interfaces may also require finite-index generalizations when
these two new helper modules are proved.

## Users

The table lists declaration users and direct importers of the old helper modules.
There is no change to either old module's source or interface, so their consumers
need no adaptation or recompilation against an altered dependency.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.CohomologyColimitFiniteCoverSites | K6 | Uses new finite helpers privately; statement unchanged. |
| Sheaf.CategoryTheory.CohomologyColimitSites | unclaimed | Old imports and applications remain valid verbatim. |
| Sheaf.CategoryTheory.CohomologyColimitSitesCorrectedLift | unclaimed | Old class-descent import and application remain valid verbatim. |
| Sheaf.CategoryTheory.CohomologyColimitSitesClassDescent | unclaimed | Original declaration and proof preserved verbatim. |
| Sheaf.CategoryTheory.CohomologyColimitSitesEventualVanishing | unclaimed | Original declaration and proof preserved verbatim. |

All transitive consumers see exactly the previous public interface. The new
helper modules publicly import the statement prerequisites and expose only their
own new theorem. The assigned module imports them privately.

## Status

landed 20261026T091921-L-3387028 2026-10-26 (merge of deliver/K6/Sheaf.CategoryTheory.CohomologyColimitFiniteCoverSites)
