## What changed

Restored Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence from the exact
quarantine path named by coord/rework.tsv. Preserved its theorem signature and
complete proof, replacing the obsolete FilteredObject.HomPreservingSteps.hom
proof expression with the current category-morphism .hom projection.

Changed the DoubleComplexTotal imports in the three unclaimed homotopy dependency
modules to WeilConjectures.CategoryTheory.DoubleComplexTotal. The presentations and
two-column-image theorem already import that adopted provider. This removes the
reproduced duplicate-constant import failure. The dependency declarations and
proof bodies are unchanged. All changes are under Sheaf; no source-library file
or target was edited. The change record is
coord/changes/v3-cartan-eilenberg-comparison-independence-restoration.md.

Preserved the main node's dependencies and recorded the restoration in its
proof-origin note. Updated the filtration-factorization node's provider reference
so its proof text names the module actually imported. No unit route changed.

## Proved and sorry left

This is a zero-hole restoration/repair, not a new hole closure:
CategoryTheory.cartanEilenberg_comparison_independence has zero holes in the
quarantine archive and zero holes after repair. Holes closed: zero. Holes added:
zero. No theorem was split off.

One existing dependency hole is retained verbatim in the adapted module:
CategoryTheory.cartanEilenberg_doubleComplex_homotopy_components
(lem-sp-cartan-eilenberg-double-complex-homotopy-components). It remains the whole
proof of that public theorem, with its source, proof in words, and DAG node.
It was already present before this delivery; no claim of discharging the item's
transitive axiom closure is made. The other three delivered files have no sorry.

Validation through lcompile.py --all: components 2.5 s, filtration factorization
0.0 s, homotopy 0.2 s, unchanged ComparisonHomotopy consumer 8.1 s, restored item
20.2 s. All five compiled without errors or warnings. The temporary consumer
copy was byte-identical and is excluded from the packet. All Lean lines are at
most 100 characters. Delivery preflight supplies the independent axiom probes.

## No longer needed

The four old import lines in the three dependency modules no longer use
Sheaf.CategoryTheory.DoubleComplexTotal; the public imports and the proof-only
import all now use the adopted counterpart. A source import-closure comparison
with the quarantined item finds exactly one module removed from this item's
closure: Sheaf.CategoryTheory.DoubleComplexTotal. No module is added to that
closure, and no DAG dependency is removed. def-sp-double-complex-total remains
needed and is supplied by its adopted module. This is item-local pruning;
other modules still import the Sheaf provider. No module is withdrawn.

No proof route is replaced, and no further declared dependency is pruned.
LeanFinder returned generic resolution homotopies, and Loogle confirmed
Homotopy.homologyMap_eq in Mathlib.Algebra.Homology.Homotopy. Source searches found
no replacement for the whole CE comparison-independence theorem. The complete
archived implementation already uses those shorter Mathlib tools where applicable.

## Where the brief, the DAG or earlier work was wrong

The item is a listed restoration with zero textual holes, rather than an
unproved statement. The complete quarantined proof is retained. Its failed
cluster restoration had stale duplicate-provider imports in three dependencies,
plus the obsolete accessor in the proof. Both failures were reproduced and
repaired; a compiling no-op or rebase would not fix either one.

The filtration-factorization node still named the Sheaf private-helper provider;
it now names WeilConjectures.CategoryTheory.DoubleComplexTotal. Its finite-sum
argument and dependencies remain intact. The main node's inherited unit is
sk-prop-av-pqf-finite, whose realized lists contain no CE step; no unit record or
route was changed. No new statement, definition, or node is introduced.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
