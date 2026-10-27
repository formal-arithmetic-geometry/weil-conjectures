## What changed

Proved `AlgebraicGeometry.ProEtale.VectorIntegrationSite.projectiveB_isIso` in
`Sheaf.Paper.ProEtaleProjectiveLineTrace`. Private proved helpers establish the
adjunction mate identity, identify the unit and Chern pushforward components,
and assemble their biproduct. The resulting arrow is the existing
`geoP1TwistedMap`, whose invertibility is already proved.

The proof imports `Sheaf.Paper.SupportedProjectiveChernComparison` for the stated
Chern comparison and privately imports all of
`Sheaf.AlgebraicGeometry.GeoP1Cohomology` to use its proved `twisted_isIso` helper.
All existing signatures, non-theorem bodies, attributes, docstrings and public
imports are preserved. No consumer or source-library module changes. Updated the
item's DAG proof and dependencies to match this argument. Proof-context settings
are recorded in `coord/changes/E5-projective-line-trace-proof-context.md`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.VectorIntegrationSite.projectiveB_isIso`
(node `def-pur-supported-projective-site-arrows`). Added 0 holes; split off 0
statements. All private helpers are proved. No `sorry` remains in the delivered
Lean module.

Validation: the final module compiled through `lcompile.py` in 27.4 seconds
with exit code 0, including the existing Chern comparison dependency in the
private overlay.

The proof uses the existing stated
`AlgebraicGeometry.ProEtale.VectorIntegrationSite.supportedProjectiveChern_comparison`
(node `lem-pur-supported-projective-chern-comparison`), which currently has its own
`sorry` in the shared library. That existing dependency is not a new hole of this
delivery and remains a separate stage-3 item.

## No longer needed

No original public import, shared node or shared module is removed or withdrawn.
The original node had no numbered proof or proof dependencies. Its new dependencies
record the actual component-comparison argument. The unit route and the existing
`projectiveTrace` definition are retained.

The final proof does not directly import `AdicPurityRootComparisons`, construct the
infinity divisor-line identification, or expand the Cartier Ext realization. Those
are internal ingredients of the existing supported Chern comparison theorem.
The exploratory new modules `ProjectiveLineInfinityDivisor` and
`OrdinaryFiniteClassHom` and their nodes were never delivered and are excluded
from this packet; the imported existing theorem supplies the required interface.
This does not assert that its own dependencies can be pruned.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. During this session, the shared library acquired the
precise supported Chern comparison interface in a separate delivery (its node
records landing `20261025T202406-L-2713318`). Reusing that declaration gives the
requested proof from stated dependencies. The direct duplicate Chern calculation
was unnecessary and caused expensive conversions between derived-category instance
representations; it is absent from the final proof.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
