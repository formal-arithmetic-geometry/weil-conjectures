## What changed

Restored `lean/Sheaf/AlgebraicGeometry/FieldFibreHomology.lean` as a public re-export
of `WeilConjectures.AlgebraicGeometry.FieldFibreHomology`. The upstream module already
proves `AlgebraicGeometry.Scheme.Modules.single_field_fibre_homology` with the exact
same signature (checked byte-for-byte). Removed the duplicate theorem body and its
three private helpers. The two original public imports stay verbatim.

Reattached node `new-field-fibre-homology` to the existing upstream declaration.
Its proof, proof dependencies, and mathematical statement remain correct unchanged:
upstream uses the same bounded-flat comparison and single-cohomology argument.
No upstream source file or declaration is edited. The change record is
`coord/changes/field-fibre-homology-upstream-reexport.md`.

Compared all eight imports of the quarantined module with the upstream module:
the sets are exactly equal. Therefore this re-export does not introduce dependency
twins. The older DIFFERENT classification in the retirement inventory was checked
rather than assumed to describe today's imports. The supported source boundary
is respected: the existing upstream theorem remains intact.

## Proved and sorry left

Zero-hole repair: the quarantined module had 0 holes and the delivery adds 0 holes.
Closed 0 of 0 sorries; split off 0 statements. The public theorem is provided by its
already proved upstream declaration, rather than stated again or weakened.

The first repair qualified the five references to AlgebraicGeometry.derivedPullback
and compiled in 16.8 seconds, passing the delivery dry run. An ordinary recheck
compiled in 17.6 seconds. Subsequent delivery axiom-probe compiles timed out;
profiling and a direct print-axioms diagnostic also timed out without diagnostics.
Those exploratory edits and diagnostics are not delivered. The final route uses
the existing upstream proof with no duplicate declarations to elaborate or audit.
Final server compilation and preflight are performed by lcompile.py and deliver3.py.

## No longer needed

The duplicate private helpers flat_of_finiteLocallyFree, flat_complex_pullback_iso,
and flat_single_pullback_iso are removed from the Sheaf module. The identical public
theorem is retained upstream. No upstream declaration or proof is removed.

The following explicit proof-only imports are removed from the Sheaf forwarding
module; upstream retains all six, so none of these dependency modules is globally
pruned:

- WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
- WeilConjectures.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact
- WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
- Mathlib.Algebra.Homology.DerivedCategory.TStructure
- WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
- WeilConjectures.CategoryTheory.Abelian.Flat.Basic

No DAG proof dependency is pruned. No new nodes are introduced. The Sheaf module
is a compatibility import path, and the existing upstream declaration is the single
implementation.

## Where the brief, the DAG or earlier work was wrong

The assigned file is in quarantine, not lean/: coord/rework.tsv records the sync
failure caused by the more-local Scheme.Modules.derivedPullback name. This item
needs a compile repair and honest zero-hole accounting, rather than a fresh proof.
Upstream already fixed the name resolution by qualifying AlgebraicGeometry.

The retirement inventory's reason for keeping this twin (different dependency
copies) is obsolete for the current files: both import exactly the same modules.
The public statement is byte-for-byte identical. Reusing the existing theorem is
therefore the shortest route and avoids duplicate declarations and proof traversal.
The unit route is unchanged because the reused proof is the same argument.

No live or quarantined module imports the Sheaf item (rg search). The only other
textual consumer of single_field_fibre_homology is the upstream
WeilConjectures.AlgebraicGeometry.FiniteFreeSingleFieldFibre, already importing the
upstream theorem. tools/downstream.py reports "unknown module(s)" for the Sheaf
item because it is quarantined; this is why the explicit import/usage search was
also made. No consumer requires adaptation and no target signature changes.

The three msearch.py searches (grep, Lean Finder, Loogle) were run. The exact match
was found by reading the upstream module, so no intermediate statements are needed.
Rank zero, empty schemes, and degrees outside support keep the same treatment in
the existing upstream proof; no flatness hypothesis on the map to the field is added.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
