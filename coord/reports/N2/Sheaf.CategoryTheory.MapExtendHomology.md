## What changed

Removed the duplicate private `mapExtendTermIso`, `mapExtendTermIso_comm`, and
`mapExtendComplexIso`. The public theorem now uses the existing
`HomologicalComplex.mapExtendIso`, followed by `homologyFunctor.mapIso` and
`extendHomologyIso`. Added the proof-only import
`WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap`.
The public theorem signature and public imports remain identical. Updated the
module docstring and the node proof metadata to match this route.

## Proved and sorry left

`mapExtendHomology_nonempty_iso` is fully proved. Holes closed: zero; holes added:
zero; sorry left: none. This is the assigned zero-hole duplicate repair.
The sandbox module compiles with `lcompile.py`; the source axiom probe reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed `mapExtendTermIso`, `mapExtendTermIso_comm`, and `mapExtendComplexIso`.
No dependency nodes or modules are pruned; the canonical `mapExtendIso` supplies
the component and differential checks.

## Where the brief, the DAG or earlier work was wrong

Upstream review #1424 correctly identified the duplicate constructions. The only
caller of the private helpers was this module's theorem; it now uses the upstream
construction. `Sheaf.Paper.FreeRepresentableHomotopyHomology` uses the unchanged
public theorem signature and needs no adaptation. No target or statement changed.

The prescribed dry run
`python3 /home/ubuntu/weil-launcher/deliver3.py N2 Sheaf.CategoryTheory.MapExtendHomology --no-push`
printed `OK` on 2026-10-14.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader. The module, node statement, unchanged
public theorem signature, and canonical `HomologicalComplex.mapExtendIso` route
were checked by the worker; no new statements or sorries were introduced.

The duplicate repair is recorded in `coord/changes/map-extend-homology.md`.

## Second reading by N2

1. Compared the delivered module with the repository version. The public theorem
   `mapExtendHomology_nonempty_iso` has the identical signature; only private helper
   declarations, the proof-only import, and proof text/metadata changed. Verdict: pass.
2. Compiled the module and the axiom probe with `lcompile.py`. The module has no
   `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; the theorem's
   axioms are only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Checked the canonical `HomologicalComplex.mapExtendIso` route against its source
   and searched the library for existing declarations. No new split-off statement was
   added, and the existing node remains true and unchanged in interface. Verdict: pass.
4. Checked pruning and imports. The three private duplicate helpers are no longer
   needed; `WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap` is imported
   privately because it is used only by the proof, while all public imports remain.
   The unit route still proceeds through the map-extend isomorphism and
   `extendHomologyIso`; no dependency node or module is pruned. Verdict: pass.
5. Checked the DAG node proof and proof origin against the Lean proof. The node now
   records `mapExtendIso`, homology functor mapping, and `extendHomologyIso`, with no
   added holes or weakened statement. Verdict: pass.

Changed: appended this independent second-reading record; no mathematical or
interface changes were required.
