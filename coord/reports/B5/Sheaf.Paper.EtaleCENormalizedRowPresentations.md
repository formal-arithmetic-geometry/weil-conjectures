## What changed

Repaired the current stale-base return for delivery `d00cb6c744`
(base `1d80189a2`, return dated 2026-10-20 14:12 UTC).
At this retry the shared checkout still has no library-path copy of the item.
Read the current rework row and B5 claim/return records before comparing the
retained packet with its complete current source,
`quarantine/Sheaf/Paper/EtaleCENormalizedRowPresentations.lean`, and current DAG
node. The retained Lean differences are precisely the API and elaboration
repairs below; no independent archive change is overwritten. The delivery tool
constructs the replacement commit on freshly fetched main. The restoration
retains the archive's public interface and proof plan.

Restored the quarantined module `Sheaf.Paper.EtaleCENormalizedRowPresentations`
to its original library path, repairing the removed
`CategoryTheory.Functor.kInjective_computes` call in
`AlgebraicGeometry.Etale.exists_etaleCE_normalized_row_presentations`.

Package the total resolution and canonical resolution as
`CochainComplex.KInjectiveResolution` values. Use their proved `homotopyEquiv`
directly, retaining its comparison maps and inverse homotopies, and
`homotopyEquivHomotopy` for
the augmentation square. The normalization calculation explicitly exposes the
spectral-sequence fields before simplification, avoiding expansion of the entire
presentation record. Page-zero compatibility and negative-page vanishing use
their definitionally matching proofs directly; subquotient comparisons evaluate
the existing page isomorphism instead of simplifying the page construction.
The coefficient-naturality helper now composes the Ext-class, sections-class,
map-extension and extension-homology naturality squares using `CommSq.vert_comp`.
`CommSq.vert_inv` cancels the inverse comparisons. This avoids simplifier matching
through the composite comparison's large definition and allows the helper to
respect ordinary transparency.
The signed-row and finite-filtration arguments are unchanged. Added private proof
imports `WeilConjectures.Algebra.Homology.KInjectiveResolution` and
`Mathlib.CategoryTheory.CommSq`.

The existing theorem signature, all public imports, all definitions and existing
docstrings are unchanged. Updated the existing node's first proof step and
`proof_origin` to identify the replacement API and the square-composition proof.
No new nodes or statements.

Validation: the final retained module compiles against current dependencies
through `lcompile.py` in 25.6 seconds, without warnings. It uses the canonical
`homotopyEquiv` directly instead of rebuilding it from its fields. The required
delivery dry run additionally checks the declaration axioms.
Compared the complete main-theorem signature and public-import list against the
quarantined baseline: identical. All Lean lines are at most 100 characters.
An earlier instrumented compile timed out at 60 seconds. Profiling experiments
and the explicit normalization calculation were confined to this sandbox; the
delivery contains no profiling commands or temporary proof holes.

## Proved and sorry left

This is a build repair of an existing proved declaration, not a newly closed hole.
The quarantined baseline had zero `sorry`s; the repaired module has zero `sorry`s.
Holes closed: none (0 of 0). Holes added: none. Split-off statements: none.

The complete proofs of
`AlgebraicGeometry.Etale.exists_etaleCE_normalized_row_presentations`
(node `lem-weil-pbc-ce-normalized-row-presentations`) and the private
`ordinary_coefficient_naturality` are retained. The removed API call is replaced
by the existing proved K-injective-resolution construction.

## No longer needed

No import was removed; no module or DAG branch is claimed as pruned.
The legacy declaration `CategoryTheory.Functor.kInjective_computes` is no longer
used. Its mathematical K-injective uniqueness step is retained using the
canonical source-library API, so the dependency node
`lem-sp-kinjective-computes` remains in the proof plan.

The other quarantined modules in this cluster all depend, directly or indirectly,
on the separate quarantined root `Sheaf.Paper.EtaleCERowCyclesNaturality`.
They cannot be compiled or restored from this root repair alone; none is changed
or added to this delivery.

## Where the brief, the DAG or earlier work was wrong

This item is listed in `coord/rework.tsv`, not a remaining proof hole. The module
is absent from `lean/` because the upstream sync quarantined it; its baseline is
`quarantine/Sheaf/Paper/EtaleCENormalizedRowPresentations.lean`.
The recorded failure is the unknown constant `Functor.kInjective_computes`.
The dependency node still attaches that legacy name, while the canonical
source-library module now provides `KInjectiveResolution.homotopyEquiv` and
`homotopyEquivHomotopy`, realizing the uniqueness step actually needed here.

The source-library twin already demonstrates this API replacement. Its public
imports use canonical upstream presentations, whereas this quarantined module
retains its existing Sheaf presentation interface. The repair follows that
construction without importing the twin or introducing a conflicting theorem.
No target, unit route, statement or data definition is changed.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
