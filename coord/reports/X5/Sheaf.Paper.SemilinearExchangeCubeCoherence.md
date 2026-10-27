## What changed

Reduced `WeilConjectures.PodExchangeCube.rational_coherence` and
`WeilConjectures.PodExchangeCube.common_coherence` to the underlying ordinary,
compact-support and refinement cube component equations at their respective
coefficient stages. The assembly proof is complete: it proves the Weil-pair
morphism equation by naturality at the actual Weil isomorphism, proves closure
under composition and both whiskerings, proves the exchange representative-change
identity from `comparison_trans`, and proves the composition representative-change
identity from `composition_comparison` with transport across `fiberModels.map_comp`.
The seven-clause `Laws` package is assembled from these proofs and the five raw
cube clauses. No inverse to a general exchange is used.

Moved the 17 existing prerequisite declarations, including the already proved
`relabeling`, to `Sheaf.Paper.SemilinearExchangeCubeData` and publicly re-exported
them from the original module. All 19 original declaration signatures and every
non-theorem body were compared mechanically and agree after whitespace
normalization. This breaks the otherwise circular dependency between the new
component proof items and their assembly theorem. It is a dependency refactor,
not a response to a compile-time limit. Neither target statements nor their
meaning changes. The prerequisite owner tag is added to the `Comparisons` docstring; all other
original declaration docstrings are retained. The change record is
`coord/changes/X5-semilinear-exchange-cube-prerequisites.md`.

Read the eight DAG proof steps, all declared dependency interfaces, and the
current blueprint's `lem-fix-weil-operations.proof.md` and
`prop-weil-operations.proof.md`. Lean Finder, Loogle, LeanSearch and local rg
found generic naturality, mate and fixed-pair transport lemmas but no theorem
already specializing the canonical coefficient exchange laws to these normalized
supplied operation data. The assembly uses the existing operation-stage cocycle
and composition comparison fields directly.

## Proved and sorry left

Closed the two original theorem bodies, unchanged in signature:

- `WeilConjectures.PodExchangeCube.rational_coherence`.
- `WeilConjectures.PodExchangeCube.common_coherence`.

This is a decomposition, not a claim that the six remaining component cube proofs
are finished: two original holes closed, six holes added, net minus four holes.
No sorry remains in the original item module or the prerequisite module.
Every remaining hole is exactly `:= by sorry`, in a separate new module, with a
source, proof in words and corresponding DAG node:

- `WeilConjectures.PodExchangeCube.rational_ordinary_cubes`:
  `lem-pod-semilinear-rational-ordinary-cubes`.
- `WeilConjectures.PodExchangeCube.rational_support_cubes`:
  `lem-pod-semilinear-rational-support-cubes`.
- `WeilConjectures.PodExchangeCube.rational_refinement_cubes`:
  `lem-pod-semilinear-rational-refinement-cubes`.
- `WeilConjectures.PodExchangeCube.common_ordinary_cubes`:
  `lem-pod-semilinear-common-ordinary-cubes`.
- `WeilConjectures.PodExchangeCube.common_support_cubes`:
  `lem-pod-semilinear-common-support-cubes`.
- `WeilConjectures.PodExchangeCube.common_refinement_cubes`:
  `lem-pod-semilinear-common-refinement-cubes`.

Each is strictly a portion of the original argument. The ordinary theorem states
only exchange and direct composition cube components; the support theorem only
compact exchange and support composition components; the refinement theorem only
refinement cube components. None states a fixed-pair equation or either full
representative-change compatibility conclusion. The assembly proves those parts.

Edge cases checked before stating the component lemmas: identity morphisms,
identity compactification comparisons, the empty scheme, zero coefficient
objects, distinct model compactification anchors, and model schemes with
nonseparated structural maps. All equations remain well typed with exactly the
original domains. Relative properness is sufficient; no structural separatedness,
descent of geometric compactifications, or stable integral lattice for arbitrary
Weil structures is imposed. A common anchor is not assumed in refinement.

## No longer needed

No mathematical dependency node or module is withdrawn or pruned.
The existing `fix-lem-exchanges`, Frobenius-square and coefficient-operation
dependencies remain needed by the new component statements' proofs.
The original module's five public prerequisites are supplied through the new
public prerequisite module, retaining the same exported interface.
The six added imports in the original module are private proof imports.
No new component module imports `ExchangeFunctoriality` yet: its theorem body is
still sorry and its DAG explicitly records that dependency for the next worker.

## Where the brief, the DAG or earlier work was wrong

The live module already contains the proved `relabeling` from G6, so this
assignment has two original holes, not three. That proof is retained verbatim.
The blueprint's recorded old location of `prop-weil-operations.proof.md` does not
exist in the latest snapshot; the current file is under
`sec-poincare-duality/sk-thm-frobenius/`. The mathematical paragraph is unchanged.

The old plan accurately describes the mathematics but does not itself provide the
Lean transport from `exchangeFunctoriality`'s canonical coefficient operations to
the supplied normalized operation datum. That work is now exposed as six precise
component items, rather than left buried in two opaque whole-package holes.
The unit's `realized` fields are unchanged, as is every parent dependency on the
original item. Zero current Lean importers is not used as a withdrawal argument.

## New nodes

`def-pod-semilinear-exchange-cube-data` records the unchanged prerequisite
interface moved to the new data module; it introduces no new operation or data
choice. The change record above covers the move and public re-export.

`lem-pod-semilinear-rational-ordinary-cubes` and
`lem-pod-semilinear-common-ordinary-cubes` isolate parent proof steps 3--4:
the ordinary cube from square naturality and the direct compositor from vertical
pasting, transported through the coefficient comparisons.

`lem-pod-semilinear-rational-support-cubes` and
`lem-pod-semilinear-common-support-cubes` isolate the compact-support parts of
steps 3--5, using the proper/open Frobenius cube and composition rectangle with
independent model anchors and arbitrary geometric representatives.

`lem-pod-semilinear-rational-refinement-cubes` and
`lem-pod-semilinear-common-refinement-cubes` isolate steps 5--6: base-changed
refinements commute with the Frobenius exchange even between distinct anchors.
All six follow the current `lem-fix-weil-operations.proof.md` composition/exchange
paragraph; their docstrings and nodes give the complete remaining argument.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
