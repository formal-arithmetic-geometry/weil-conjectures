## What changed

Retired the duplicate module `Sheaf.AlgebraicGeometry.AffineSpectrumCounitCompatibility`
and repointed `lem-pc-affine-spectrum-counit-compatibility` to
`WeilConjectures.AlgebraicGeometry.AffineSpectrumCounitCompatibility`, declaration
`AlgebraicGeometry.affineSpectrum_counit_compatibility`.
The complete declaration, including its proof, is byte-identical in the two current files.
The adopted source module, its declarations, imports, and proofs are untouched.

Checked the live item and the rework row before editing: M8's repair has already landed,
and the live Sheaf module compiles without warnings in 12.1 seconds. This delivery removes
the remaining duplicate rather than resubmitting that repair. The quarantine archive is
preserved. Change record: `coord/changes/S8-affine-spectrum-counit-upstream-duplicate.md`.

The replacement is the existing complete upstream proof from the generic coordinate counit
theorem and comparison cancellation. A server-compiled example with the original statement
is proved by `exact affineSpectrum_counit_compatibility f K`, importing only the upstream
module. It compiles in 2.0 seconds; `#print axioms` lists exactly `propext`,
`Classical.choice`, and `Quot.sound`.

## Proved and sorry left

The item has zero direct holes before this delivery and zero afterward. Closed: none.
Added: none. Split off: none. The preserved upstream declaration
`AlgebraicGeometry.affineSpectrum_counit_compatibility` is fully proved, including its
transitive dependencies according to the compiler's axiom check.

## No longer needed

The Sheaf duplicate module is unnecessary and is withdrawn through `deleted.txt`.
Its three public imports (upstream `AffineSpectrumDirectImageCoordinates`,
`SchemeDerivedMateEvaluation`, and `AffineSpectrumComparisonCancellation`) and its private
import (upstream `AffineSpectrumCoordinateCounit`) disappear from the empty retired module.
Those dependencies remain necessary for the preserved upstream proof: none of their nodes,
declarations, or modules is withdrawn.

There are no live or quarantined Lean importers of the Sheaf item. This is not the sole
reason for withdrawal: the parent node `lem-pc-affine-spectrum-mate-compatibility` continues
to use the same counit node in steps 2 and 3, now attached to the identical upstream theorem.
Its Lean module already imports the upstream counit module and applies the same declaration
at `f` and `f'`. No parent import or dependency must change. The unit record
`sk-thm-picard-semicon` has no realized step identifying this module; the mathematical route
and every proof dependency are preserved.

## Where the brief, the DAG or earlier work was wrong

The dispatch is stale as a proof/rework assignment: the current live item has no `sorry`,
the invalid local irreducibility command is already removed by M8, and its complete proof
has an adopted upstream duplicate. The DAG alone still pointed to the redundant Sheaf copy.
This delivery corrects that attachment and retires only that copy. No definition, theorem
statement, target, or mathematical proof route changes.

Searches run in this session: LeanFinder returned eight generic mate/counit results;
Loogle found `CategoryTheory.conjugateEquiv_counit`; the launcher grep returned no hits.
Direct `rg` over both library roots found the exact upstream theorem and its actual parent
consumer. The exact source theorem supersedes the generic search results for this item.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
