## What changed

Reduced `CategoryTheory.CondensedBar.internal_bar_finite_index_transfer` to the
coefficient-module finite-coset construction. Its existing statement and all supporting
public definitions are unchanged. Added the proof-only import
`Sheaf.CategoryTheory.InternalBarCoefficientTransfer`.

The item now constructs natural transformations of double-complex functors by applying
`NatTrans.mapHomologicalComplex` and flipping. It constructs the horizontal homotopy
componentwise from the coefficient homotopy. Coefficient naturality proves that each
homotopy component commutes with the vertical differential, and proves naturality for
all coefficient chain maps. Applying the additive internal homology functor gives the
specified homotopy on vertical cohomology. Mathlib's `Homotopy.homologyMap_eq` gives the
index identity on subsequent horizontal cohomology.

Validation: the required remote `lcompile.py --all` compiled both modules without
warnings: 1.1 seconds for the coefficient statement and 15.5 seconds for the item.
The original theorem statement was also compared byte-for-byte and is unchanged.

This is a decomposition, with one upper hole replaced by one strictly smaller
coefficient-module construction. The new statement has no coefficient complex, second
differential, vertical cohomology, or iterated cohomology. The extension to arbitrary
complexes and both cohomology assertions is proved here, rather than included in that
remaining hole. No definition chooses data from an existence theorem: the existential
coefficient maps are eliminated only in the theorem proof, and the private constructors
are explicit and take their maps and homotopies as arguments.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.CondensedBar.internal_bar_finite_index_transfer`
(node `lem-sfb-internal-bar-row-finite-index-transfer`).

Added one hole:
`CategoryTheory.CondensedBar.internal_bar_coefficient_transfer`
in `Sheaf.CategoryTheory.InternalBarCoefficientTransfer`
(node `lem-sfb-internal-bar-coefficient-transfer`). Its docstring and node contain
the full finite-coset and prism argument. The item has zero remaining `sorry`s;
the new module has exactly one. Net holes closed: zero (decomposition).

The private constructors `transferDoubleMap` and `transferDoubleHomotopy` are complete.
The latter's vertical chain-map law is exactly coefficient naturality applied to
`I.d q q'`; its boundary and zero laws are the coefficient homotopy laws at `I.X q`.
The internal homology argument preserves all integral multiples and uses no division,
injectivity, resolution, or sectionwise exactness hypothesis. Edge cases retain the
original statement: zero coefficients, zero complex, zero ring, degree zero, trivial
group, H=G, and non-normal H.

## No longer needed

Removed the unused proof import `WeilConjectures.CategoryTheory.DoubleComplexTotal`;
the actual double-complex and homology API is already exposed through Mathlib imports.
No whole-library module withdrawal is claimed.

No mathematical dependencies of the finite-coset route are pruned. The homogeneous
coordinates, finite transversal/retraction and vertex prism remain dependencies of
the new coefficient construction, so they have moved down one node rather than
becoming unused. The original item now directly depends on that construction and
on the recorded bar and double-complex conventions. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or target change was found. There is a Lean-interface limitation
in the planned use of the coordinate lemma: it requests a family of bar diagrams
for every profinite group, whereas this item supplies just B and B_H. The finite-coset
averaging theorem is about topological vector spaces, not internal module sheaves;
only its group-theoretic transversal and retraction clauses apply directly here.
The remaining coefficient statement records the internal finite-sum and homogeneous
prism construction needed to bridge these interfaces, with the original proof in
words preserved. It is not a claimed application of topological averaging to
arbitrary internal modules.

The latest blueprint paragraph (3) motivates this auxiliary argument rather than
stating it verbatim; the inherited source and the new node are explicitly marked
agent-written. `blueprint_refs.py ancestor` returns None for this created-node chain;
the new node preserves that ancestry and the exact paragraph, and the blueprint
search found no duplicate coefficient-level assertion.

## New nodes

`lem-sfb-internal-bar-coefficient-transfer`, module
`Sheaf.CategoryTheory.InternalBarCoefficientTransfer`, isolates original proof steps
1--4 for individual coefficient modules. Its proof retains the existing homogeneous
coordinate, finite-coset averaging and vertex-prism nodes. The new node carries actual
LeanFinder, Loogle and Mathlib grep results, source, a complete proof, and its exact
Lean declaration. The parent node's proof and proof dependencies now describe the
componentwise lifting and additive homology argument. No shared interface changes
or change records are needed.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
