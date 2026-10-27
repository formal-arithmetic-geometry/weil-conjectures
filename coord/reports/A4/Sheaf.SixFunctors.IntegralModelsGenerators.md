## What changed

Restored the complete quarantined module from
`quarantine/Sheaf/SixFunctors/IntegralModelsGenerators.lean`, as required by its
2026-10-22 rework entry. Repaired the private proof import for
`CategoryTheory.Mod.relativeTensorRightIso`: the upstream module is imported
normally, and its relocated project additions are imported with `import all
Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian`.
The helper used by `integralModel_locallyFree_flat` and `integralModel_flat_detect`
is defined privately in that current home, not in the upstream module.

An exact source comparison against the archive verifies that these import lines
are the entire Lean change. All public imports, declaration signatures,
definitions, instances, theorem proofs, and the six-step argument are unchanged.
The existing generator and definition DAG attachments and dependencies are retained;
no node update is needed because the mathematical proof route is unchanged.
The repair and seven unchanged quarantined direct importers are recorded in
`coord/changes/A4-integral-model-tensor-comparison-import.md`.

Validation: the entire 1,460-line module compiled without errors or warnings on
the project server through `LCOMPILE_NO_LOCAL=1 lcompile.py` in 21.0 seconds,
under the unchanged 60-second limit. Import-direction checking found no cycle.
Temporary diagnostic files remain outside the delivery's `lean/` tree; no
profiling option or partial proof is in the delivered module.

## Proved and sorry left

This is a repair of a previously proved, quarantined module: 0 original holes,
0 holes closed, 0 holes added, 0 holes remaining. The full existing proof of
`WeilConjectures.SixFunctors.integral_models_generators`
(node `det-lem-integral-models-generators`) is retained, including all three clauses.
Both private flatness lemmas remain fully proved. No new declaration or split-off
result is added.

## No longer needed

Private access through `import all
WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian` is replaced by
an ordinary upstream import and a private import from the actual relocated home.
No mathematical dependency, DAG node, module, public import, or declaration is
pruned or withdrawn.

## Where the brief, the DAG or earlier work was wrong

The rework row records an overloaded-name failure at archive line 501, which uses
`Mod.relativeTensorRightIso`. Source inspection shows that this private helper
moved to `Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian`.
An import diagnostic against the current server confirmed that the old imports
alone no longer expose `CategoryTheory.Mod.relativeTensorRightIso`; importing its
current home resolves all four uses while preserving the entire original proof.
No definition repair or change to the DAG's mathematics is required.

Mathlib search found the generic finite-limit transport lemma
`CategoryTheory.Limits.preservesFiniteLimits_of_natIso`; other hits concern
ordinary module categories. The project's existing relative-tensor comparison
is reused from its current module, without duplicating any construction.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
