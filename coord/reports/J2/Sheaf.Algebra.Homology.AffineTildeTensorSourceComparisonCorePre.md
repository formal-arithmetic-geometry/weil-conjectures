## What changed

Retired the assigned zero-hole Sheaf precomparison compatibility wrapper in
favor of its complete adopted source implementation. Its sole direct consumer,
`Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCoreFinal` (holder K7),
changes only line 8: the retired import becomes the legacy tilde-normalization
import. Its existing source core-final import exports the canonical
precomparison and all comparison data. All other consumer lines are unchanged.
No source-library file, quarantine archive, target or node is changed.

The legacy precomparison and core-final signatures were stated in scratch Lean
and proved by applying the existing source theorems. Complete source proofs
remain in place, with only the three permitted axioms. A normalized textual
comparison also verifies the legacy precomparison signature and the entire
core-final theorem/proof, after expanding the legacy tilde abbreviation.

Change record: `coord/changes/J2-affine-tilde-source-precomparison-retirement.md`.

## Proved and sorry left

Zero-hole retirement repair: proved 0 of 0 item holes; holes closed: none;
holes added: none; split off: none. No delivered declaration contains `sorry`.
The complete adopted source proof
`AlgebraicGeometry.affineTildeTensorSourcePrecomparison` is retained, as are
`AlgebraicGeometry.exists_affineTildeTensorSourceComparisonCore`,
`affineTilde_scalarExtension_comparison`, `affineTilde_pushforward_unit_isIso`
and `leftCounit_naturality`. Axiom checks show only `propext`,
`Classical.choice` and `Quot.sound`.

## No longer needed

Retired module:
`Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre`.
The direct consumer now obtains its proved declarations through
`WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparisonCoreFinal`.
Its sole import of the retired module is replaced by the legacy normalization
import, keeping `affineTildeFunctor` and its zero-map instance available.

Removing the redundant wrapper also removes its six direct import lines:
`Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization`,
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
`WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility`,
`Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePreBase`,
`Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonHelpers`, and
`WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre`.
Their mathematical declarations remain available through the canonical source
chain. The two Sheaf prebase/helper wrappers become unnecessary on this route;
they are not deleted by this packet.

No mathematical dependency or DAG node is pruned. K-flat resolution,
scalar-extension counit comparison, affine pushforward-unit invertibility,
and derived-unit compatibility are retained in the source proof. The parent
node and its unit realization are unchanged.

## Where the brief, the DAG or earlier work was wrong

V5 had already completed the zero-hole quarantine restoration. The current
assignment is the retirement row in `coord/retire-items.tsv`; repeating V5's
wrapper unchanged would be a no-op. This packet performs that retirement and
migrates the actual direct consumer, retaining quarantined parent dependencies.

Shared source and claims changed during the session. Initial preflight returned
a broader packet because the quarantined outer parent was classified as new,
and K7 had taken the core-final consumer. That packet was discarded. The final
packet touches only the assigned retirement and the one forced import line in
K7's current consumer. The outer parent held by W6 and its existing DAG node
are not changed. No mathematical statement is disputed and no new node is needed.

## Forced adaptations

`Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCoreFinal` is held by K7.
Its original line 8 imports the explicitly withdrawn module, so it cannot
compile after the item's removal: the corresponding object file no longer
exists. Old baseline compiled artifacts do not supply a valid post-retirement
counterfactual. The official delivery tool records this withdrawal condition.

Only line 8 changes, replacing the retired wrapper import with
`Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization`.
That import preserves the legacy tilde abbreviation needed by existing caller
signatures. The consumer's unchanged public source core-final import already
supplies the precomparison and all mathematical dependencies. Every other
line, signature, visibility, import and docstring is byte-identical to the
current K7-held module. The adapted module compiles; the independent reader
checks both the withdrawal counterfactual and the minimal diff.

## Forced adaptations

### Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCoreFinal
Original imports module(s) explicitly withdrawn in deleted.txt: Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre. Those imports must be migrated in this delivery; the baseline's compiled copies are not valid counterfactual dependencies. Adapted module compiled in the delivered set. CODEX verifies the migration and every accompanying API adaptation is needed.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
