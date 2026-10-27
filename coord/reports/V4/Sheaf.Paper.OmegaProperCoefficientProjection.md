## What changed

The item module now proves `omegaProperCoefficientProjection_isIso` by applying
`DerivedCategory.isIso_iff` to the homology-level comparison theorem. A new module,
`Sheaf.Paper.OmegaProperCoefficientProjectionHomology`, states the strictly smaller
homology-level claim and is imported privately by the item module. The item node's
proof and `proof_deps` now record this route, and a node was added for the new theorem.

## Proved and sorry left

The original hole in `WeilConjectures.CompactSupportCondensedRealization.omegaProperCoefficientProjection_isIso`
is closed. The delivery adds one decomposition hole,
`WeilConjectures.CompactSupportCondensedRealization.omegaProperCoefficientProjection_homology_isIso`,
recorded in node `lem-pur-omega-proper-coefficient-projection-homology`. This is a
strictly simpler statement: it asks only for the induced homology maps in each degree.
No definition contains `sorry`.

## No longer needed

The parent module no longer imports the five large proof-dependency modules from the
original plan: `lem-weil-pbc-condensed-flat-coefficient-calculus`,
`lem-weil-pbc-condensed-coefficient-complex-presentation`,
`lem-sp-finite-free-direct-image-coherence`,
`lem-weil-pbc-condensed-qcqs-pushforward-continuity`, and
`lem-weil-pbc-ring-sheaf-change-adjunction`. They remain dependencies of the new
homology-level node because its proof is the finite-stage filtered-continuity argument
described there. No other existing node or module was pruned.

## Where the brief, the DAG or earlier work was wrong

The original item proof plan describes the full finite-stage and filtered-continuity
argument but does not provide a Lean declaration for its homology-level conclusion.
The delivery makes that missing intermediate conclusion explicit and uses the existing
`DerivedCategory.isIso_iff` theorem to complete the parent proof. The target statement
and all existing declaration signatures are unchanged.

## New nodes

`lem-pur-omega-proper-coefficient-projection-homology` adds the homology-level proper
coefficient projection theorem in
`lean/Sheaf/Paper/OmegaProperCoefficientProjectionHomology.lean`; its proof is left as
one named `sorry` for a subsequent worker, with the source and complete proof plan in
its docstring and node.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
