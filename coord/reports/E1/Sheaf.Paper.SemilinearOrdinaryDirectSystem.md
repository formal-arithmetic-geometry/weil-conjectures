## What changed

Proved the original `ordinaryDirectSystem_exists` remains assembled from the core and Hom-data records, and decomposed the remaining geometric core into two strictly simpler named statements in `Sheaf.Paper.SemilinearOrdinaryDirectSystem`: `ordinaryDirectSystem_core_data_exists` for the componentwise reassembly and `ordinaryDirectSystem_core_transition_mate_exists` for the local two-component mate law. The core theorem now has a real constructor proof combining these two statements. The new `OrdinaryDirectSystemCoreData` structure and its transition predicate contain no proof holes.

## Proved and sorry left

The existing `ordinaryDirectSystem_exists` and `ordinaryDirectSystem_homData_exists` declarations remain proved. The existing `ordinaryDirectSystem_core_exists` hole is reduced by a real constructor proof to the two strictly smaller declarations below. Two `sorry`s remain, each with its own DAG node:

- `ordinaryDirectSystem_core_data_exists` (`lem-coef-ordinary-direct-system-core-components`), whose proof constructs the componentwise direct-image functor, evaluation isomorphisms, and section-carrier identities.
- `ordinaryDirectSystem_core_transition_mate_exists` (`lem-coef-ordinary-direct-system-core-transition-mate`), whose proof establishes the local mate equivalence for one horizontal square.

No `sorry` occurs in a definition.

## No longer needed

None. The core route still uses the ordinary inverse-system, semilinear system model, and normalized module-adjunction declarations. The two new nodes are the complete decomposition of the core proof and no dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

The remaining core proof bundled two independent obligations: constructing the componentwise direct-image data and proving the local transpose law for a single pair of horizontal maps. The former does not require the latter, and the latter takes the assembled datum as input. The DAG now records this strict two-step decomposition; the public core statement and all parent statements are unchanged.

## New nodes

`lem-coef-ordinary-direct-system-core-components` records the componentwise reassembly statement and is realized by `ordinaryDirectSystem_core_data_exists` in the item module. `lem-coef-ordinary-direct-system-core-transition-mate` records the local mate statement and is realized by `ordinaryDirectSystem_core_transition_mate_exists` in the item module. Both nodes include their source text, proof steps, and Mathlib searches.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
