## What changed

Restored lean/Sheaf/AlgebraicGeometry/MixedAffineSectionsPullbackUnitNormalization.lean
as a compatibility import of the complete adopted source proof in
WeilConjectures.AlgebraicGeometry.MixedAffineSectionsPullbackUnitNormalization.
The original two public imports are retained. The source theorem
AlgebraicGeometry.exists_mixedAffineSections_pullback_unit_normalization has a
byte-for-byte identical public signature to the quarantined theorem, including
its independent localization universes. No source-library file is changed.

Corrected the Lean attachment of lem-sc-mixed-affine-pullback-unit-normalization
to that source declaration. The node statement, dependencies, numbered proof,
proof origin and unit realization are unchanged. The source proof realizes the
same K-flat model, affine chart comparison and normalized-unit cancellation.
This restores the assigned module with its mathematical content available by
public import; it does not withdraw the item or create an empty module.
The quarantined source is preserved.

Change record: coord/changes/S2-mixed-affine-pullback-source-reuse.md.

## Proved and sorry left

This assigned restoration has zero original local holes and zero final local holes:
closed 0, added 0, split off 0. No new theorem or definition is introduced.
AlgebraicGeometry.exists_mixedAffineSections_pullback_unit_normalization is reused
with its existing complete source proof. No sorry remains in the restored module.
No hole is moved, no statement is weakened, and no definition chooses new data.

The compatibility module compiles with lcompile.py. The archive's theorem signature
and the adopted theorem signature were compared verbatim and agree.

## No longer needed

No mathematical node or module is pruned. In particular, every proof dependency
of lem-sc-mixed-affine-pullback-unit-normalization and the parent's dependency on
that node is preserved. The private duplicate proof and its private helpers are
not redeclared: the source implementation already supplies them.

The archived proof-only imports of Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde,
Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction,
WeilConjectures.AlgebraicGeometry.TensorPullbackTilde,
WeilConjectures.AlgebraicGeometry.MixedPullbackSectionsCounitUnit, and
Mathlib.CategoryTheory.Functor.Derived.LeftDerived are no longer needed directly
at this compatibility path. The adopted implementation imports the source versions
of the same K-flat/chart/counit dependencies and the same Mathlib derived-functor
API. Neither these modules nor their mathematical obligations are withdrawn.
Both original public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The item is quarantined, not a new unproved lemma. Its archive already has a
complete zero-sorry proof, but imports the now-withdrawn Sheaf IsKFlatTilde module.
A baseline lcompile.py run reports Unknown identifier isKFlat_tilde. The current
adopted source module proves the exact assigned statement using its IsKFlatTensor
API, and the live MixedAffineSectionsChartModelFactorization consumer already
imports and applies that source theorem. Restoring the archived declaration would
duplicate the source declaration in any combined import closure.

The DAG attachment still named the absent Sheaf declaration; this delivery attaches
it to the identical adopted declaration while retaining the mathematical proof.
Zero current importers of the absent path was not used as a withdrawal argument:
the parent node and its live source implementation still use this result.

Searches: LeanFinder returned generic affine/flatness facts, Loogle found
CategoryTheory.Functor.leftDerivedUnique, and the msearch grep returned no hits.
Direct rg on both library roots found the exact adopted theorem and its consumer.
The shorter route is therefore reuse of an already fully proved declaration.
The parent node and sk-thm-picard-duality realization were checked; no unit statement
or proof step changes. Empty schemes and zero complexes retain the same statement.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
