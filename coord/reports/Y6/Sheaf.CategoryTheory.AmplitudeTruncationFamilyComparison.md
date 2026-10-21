## What changed

Proved `DerivedCategory.amplitude_truncation_family_comparison` with its original
signature, including all four specified natural-transformation components.
The proof applies G to both individual truncation triangles and to coproducts of
those triangles. Cohomology preservation of coproducts gives the other two maps.
A proved private helper transports `Sigma.map` comparisons to the exact `colim.map`
expressions in the statement using canonical coproduct-to-colimit isomorphisms.

Private proof imports now use the existing source modules
`WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfFiniteAmplitude`,
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty`, and
`WeilConjectures.Mathlib.CategoryTheory.Triangulated.CoproductTriangle`.
The unused broad public truncation import is replaced by Mathlib's derived
t-structure module; change record:
`coord/changes/Y6-amplitude-truncation-imports.md`.
No source-library file, definition, target, or theorem signature changes.
The existing node's proof and dependencies follow this argument.

Searches used msearch leanfinder for the amplitude/truncation assertion, loogle
for `DerivedCategory.homologyFunctor`, and grep for truncation isomorphisms.
Reading the source found `CoproductsOfFiniteAmplitude`, whose bounded-comparison
theorem requires triangulated closure of P-cohomology and cannot directly apply
under this statement's weaker hypotheses. Its fully proved auxiliary lemmas do
apply. The coproduct-triangle search also used leansearch, leanfinder and grep;
Mathlib gives the dual product theorem, while the source library already proves
the exact arbitrary-coproduct theorem. No such theorem was restated in Lean.

The final source compiled cleanly with lcompile.py (7.9 seconds, exit 0).
The final delivery additionally runs
compilation and declaration/axiom preflight. No current module imports this item:
`tools/downstream.py --uses` and direct source search agree. No consumer adaptation
is needed for the public-import narrowing.

## Proved and sorry left

Closed 1 of 1 original holes:
`DerivedCategory.amplitude_truncation_family_comparison`
(node `lem-sfb-amplitude-truncation-family-comparison`).
Added 0 holes. Split off 0 unfinished statements. There are no remaining `sorry`
declarations in the delivered Lean file. The private helper
`DerivedCategory.isIso_map_colimMap_of_sigmaMap` is fully proved.
The new DAG node records an already fully proved source-library theorem and adds
no Lean declaration or proof obligation.

The argument covers empty I, c=0, zero families, and unbounded families directly.
In particular the coproduct-triangle theorem and homology preservation include
empty coproducts. No extension, kernel, or cokernel closure of P is assumed:
P-cohomology is checked for the actual truncated first vertices, then for their
coproduct, before applying hGle. Arbitrary original input cohomology bounds never
enter. Canonical coprojections prove the transport identities, so the exact
arrows in the conclusion, including all naturality, are retained.

## No longer needed

Removed private imports:
`Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`,
`Sheaf.CategoryTheory.ArrowExactColimits`, and
`WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits`.
The last module's homology-preservation instance remains available transitively
through the source-library homology/coproduct API and is still logically used;
its DAG node stays in proof_deps.

Removed the public import
`Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`, replacing it by
`Mathlib.Algebra.Homology.DerivedCategory.TStructure`. The ordinary good-truncation
notions of `def-kun-truncations` are still used via Mathlib; the unrelated
sequential homotopy-colimit predicate and its broad import closure are unnecessary
for this item. No module is withdrawn or emptied.

The proof no longer needs node `lem-sfb-arrow-exact-colimits` or its module:
it never interchanges truncation kernels/cokernels with coproducts. It also no
longer needs node `lem-kun-grothendieck-derived-coproducts` or the Sheaf wrapper
module `GrothendieckDerivedCoproductsColimit`: the already proved source-library
`preservesColimitsOfShape_homologyFunctor` supplies the needed cohomology result.
These two nodes are removed from this item's proof_deps and their obsolete
top-level tool_uses approvals are removed, preserving the homology approval. This describes local
pruning; other consumers may still need those modules. No blueprint unit step is
bypassed or changed.

## Where the brief, the DAG or earlier work was wrong

The original nine-step plan is valid but unnecessarily constructs canonical
truncation/coproduct comparisons by a degreewise kernel/cokernel argument.
Taking coproducts of the actual distinguished triangles gives the required
pre-G comparisons directly. The source library already supplies the needed
cohomology, truncation, bounds, and coproduct-triangle lemmas. Its general
bounded-comparison theorem itself is unsuitable because it asks for a
triangulated object property; this proof carefully avoids that extra assumption.
The theorem's statement is unchanged and no disputed mathematics was found.

## New nodes

`lem-sfb-coproduct-distinguished-triangles` records the already proved
`CategoryTheory.Pretriangulated.coproductTriangle_distinguished` in
`WeilConjectures.Mathlib.CategoryTheory.Triangulated.CoproductTriangle`, using
Stacks Tag 0CRG. This registers the shorter route's arbitrary-coproduct input;
it introduces no Lean module, no duplicate declaration, and no `sorry`.
The finite-sums node does not cover arbitrary I, hence was not used as a substitute.
Change record: `coord/changes/Y6-amplitude-truncation-imports.md`.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
