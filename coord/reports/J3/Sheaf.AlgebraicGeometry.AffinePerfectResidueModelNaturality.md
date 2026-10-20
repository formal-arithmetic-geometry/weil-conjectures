## What changed

Restore the quarantined `Sheaf.AlgebraicGeometry.AffinePerfectResidueModelNaturality`.
Replace the withdrawn duplicate import with
`import all WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`, reusing its proved
private counit helper. Import `WeilConjectures.AlgebraicGeometry.TensorPullbackTilde` directly for the
ordinary affine comparison.

The private `zeroMapComplexCompIso` exposes the complex-composition comparison for zero-preserving
functors. The proved private `reconstructionComparison` combines it with the reconstruction counit.
The proved private `transportedCounitComparison` transports the derived counit along an exact
functor, and `whiskeredComparison` composes the final homology factors. These categorical helpers
keep the concrete sheaf constructions out of the composition conversions.

Use the existing `affinePerfectSheafification_preservesZeroMorphisms` API, removing the unnecessary
sheafification-additivity proof and broad local additivity instance. Give the derived functors
explicit local types and pass invertibility evidence explicitly. The main proof needs no local
transparency overrides. Local irreducibility guards keep the affine-chart constructions behind
their comparison APIs. Remove the unused intermediate localization alias.

The public imports, public theorem signature and existing docstrings are unchanged. No public
definition or global attribute changes, and no consumer needs adaptation. The node retains its
attachment and original dependencies and records the directly used affine tilde formula.
Change record: `coord/changes/J3-affine-perfect-residue-local-proof-api.md`.

## Proved and sorry left

This is the listed quarantine compile repair. The archived module has zero holes and the repaired
module has zero holes: 0 of 0 closed, 0 added, 0 split off.
`AlgebraicGeometry.Scheme.affine_perfect_residue_model_naturality` retains a complete proof.
The existing private `residueTermComparison` is retained. The four new private helpers
`zeroMapComplexCompIso`, `reconstructionComparison`, `transportedCounitComparison` and
`whiskeredComparison` are complete categorical constructions from Mathlib and the existing proved
counit helper. They introduce no public interface or unfinished mathematical obligation.
The complete repaired proof compiled cleanly in 27.4 seconds with `lcompile.py`.

## No longer needed

Remove the stale proof import `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`, whose module
has already been withdrawn. Its adopted source counterpart supplies the helpers instead.
Remove the redundant private import `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`,
which is publicly imported by `ResidueTildeHomologyComparison`.
The separate sheafification-additivity construction is unnecessary for the termwise comparison.
All original mathematical dependencies remain used. No module is withdrawn, and no newly
unreachable node or module is claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The archived proof imported a withdrawn duplicate and omitted the direct adopted-source import of
`exists_tensorPullback_tilde_iso`. The repaired imports preserve the mathematical statement.

The convenience `Functor.mapHomologicalComplexCompIso` imposed an unnecessary additivity obligation
on affine sheafification; the zero-preserving comparison suffices. Constructing the longer
comparisons with concrete sheaf functors also triggered expensive unfolding. Their categorical
compositions are now checked with abstract categories in private helpers, in the same module.
The node explicitly records the affine tilde formula directly called by the proof. The unit route
is unchanged.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
