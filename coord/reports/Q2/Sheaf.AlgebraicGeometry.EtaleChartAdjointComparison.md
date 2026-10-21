## What changed

Implemented the proof of `AlgebraicGeometry.Etale.ChartAdjointComparison.exists_homEquiv` in
`Sheaf.AlgebraicGeometry.EtaleChartAdjointComparison`. The witness is exactly the inverse
of the existing `homChain`, so its specified inverse-chain identity is reflexive.
Naturality in the bounded-below test object is proved using natural isomorphisms whose
components are definitionally `leftComparison` and `closedNormalizationAmbient`, followed
by the ordinary adjunction Hom naturality equations. Naturality in the arbitrary unbounded
input follows from right-naturality of those adjunctions. All existing declaration
signatures, definitions, public imports and docstrings are preserved.

Updated the item's node proof, proof dependencies and proof origin to describe the actual
argument. The unit's chart-comparison step remains realized by exactly the original theorem.

Resumed the retained proof against current sources and checked the source adjunctions,
compact-support compatibility maps, and the unit's realized chart-comparison step.
The statement and all existing helper definitions match the current library exactly.
No launcher script or shared source was changed.

Single-file validation: `lcompile.py` compiled the final module cleanly in 19.1 seconds,
with no warning and no `sorry`. The proof of naturality in the test object applies
congruence to the comparison's naturality equation and explicitly normalizes the full
subcategory inclusion on objects. The original separated and locally-finite-type chart
hypotheses stay in the public signature; the unused-section-variable linter setting is
scoped to this theorem so retaining those original hypotheses emits no warning.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Etale.ChartAdjointComparison.exists_homEquiv`
(node `lem-sf-etale-chart-adjoint-comparison`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered module. Existing dependencies retain their own proof
status; this delivery introduces no axiom or new public declaration.

## No longer needed

Removed these four unused private proof imports:

- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`
- `Sheaf.AlgebraicGeometry.Etale.OpenExtensionZeroEtaleAdjunctionAgreement`

The existing upstream bounded-below compact-support formalism, compatibility isomorphisms
and compositors suffice for all comparison definitions. The refinement-map identification
`etaleCompactSupport_refinementComparison_eq` is not used. The conceptual compact-support
comparison dependency `lem-amb-etale-compact-comparisons` remains because its recorded
upstream compositor and compatibility declarations are used.

Removed proof dependencies and their obsolete tool approvals:
`lem-weil-pbc-open-immersion-etale`, `lem-amb-etale-adjoint-locality`,
`lem-cbc-open-extension-zero-etale-adjunction-agreement`, and
`thm-amb-etale-exceptional-adjoint`. The direct extension-by-zero derived adjunction already
has the exact Hom-equivalence type used by `homChain`; sum-extension locality and its
agreement comparison are unnecessary. The three compact-support adjunctions are explicit
hypotheses, so their existence theorem is not needed to prove this theorem. The latter
remains a statement dependency. No module is withdrawn, and no claim is made that these
modules are unused by all other targets or parents.

## Where the brief, the DAG or earlier work was wrong

The planned detour through etale sum extension and its adjunction agreement was unnecessary:
the source library already provides the unbounded derived open-extension-by-zero adjunction.
The existing `homChain` uses that adjunction directly. The previous existence-theorem import
was likewise unnecessary because `adjF`, `adjP` and `adjI` are already theorem hypotheses.
No mathematical statement or unit route was changed.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
