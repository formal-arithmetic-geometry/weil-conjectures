## What changed

Proved `TopCat.puncturedNeighborhoodCohomology_colimit` from two independent elementwise
continuity statements about its existing canonical diagram and cocone. The proof constructs
the filtered neighborhood index, represents elements of the group colimit, proves the
comparison injective by eventual vanishing, and proves it surjective by class lifting.
The colimit coprojection equations identify the comparison throughout; no unspecified
isomorphism is substituted for the canonical map.

Added one theorem per new module:
`Sheaf.Topology.PuncturedNeighborhoodCohomologyClassLift` and
`Sheaf.Topology.PuncturedNeighborhoodCohomologyEventualZero`. Each has its source,
complete mathematical proof in its docstring, and a new DAG node. Neither asserts that
the colimit comparison is an isomorphism. The parent's node follows the actual
filteredness/injectivity/surjectivity proof; the new nodes retain the spectral inverse-limit,
restriction-system, and canonical-map identification arguments of the original plan.

All existing signatures, public imports and docstrings are unchanged. No existing
definition or instance is changed, and no source-library module is edited. The new imports
of the elementwise lemmas and Mathlib's filtered-group-colimit API are private proof imports.

## Proved and sorry left

Closed the original hole in `TopCat.puncturedNeighborhoodCohomology_colimit`
(node `lem-weil-pbc-punctured-neighborhood-cohomology-colimit`). Its proof is complete Lean
and has no `sorry`.

Two new holes remain, each the entire proof of a public theorem in its own module:

- `TopCat.puncturedNeighborhood_cohomology_class_lift`, node
  `lem-weil-pbc-punctured-neighborhood-cohomology-class-lift`.
- `TopCat.puncturedNeighborhood_cohomology_eventual_zero`, node
  `lem-weil-pbc-punctured-neighborhood-cohomology-eventual-zero`.

This is a decomposition: one upper hole closed and two strictly smaller lower holes added,
not an axiom-free proof of cohomological continuity. In packet-local arithmetic the net
hole reduction is minus one; the ledger determines the targets-closure figure.
No other declaration is changed or gains a hole.

Both statements were checked on Z empty, Z equal to T, empty T, empty punctured stages,
and degree zero. The whole-space neighborhood exists even when T is empty. The empty
neighborhood is available when Z is empty. Empty-subspace cohomology groups are zero,
so neither assertion requires choosing a point of an empty space or a nonzero class.
The eventual-zero statement is asserted only for classes whose canonical image is zero;
the class-lifting statement asserts no eventual-zero property. Their combination in the
main proof is the genuine injectivity/surjectivity argument.

The initial elementwise packet compiled in 2.6 s, 5.8 s and 7.8 s for the two children
and parent respectively. The final packet removes the unused direct spectral-limit imports
and is checked again by the compilation and delivery tools.

## No longer needed

Removed the parent's private imports `Sheaf.Topology.SpectralDirectedLimit` and
`Sheaf.Topology.SpectralLimitCohomology`. The parent now consumes the two elementwise
specializations. These general mathematical dependencies are still needed by the new
children's proof plans, so this does not prune either general module or its declarations.
The parent's direct dependency on `lem-weil-pbc-spectral-limit-cohomology` is replaced
by the separate existing general class-lifting and eventual-zero results below the children.
The general isomorphism packaging is unnecessary for this route; its two mathematical
halves suffice.

No existing module is withdrawn, no upstream declaration is removed, and no UNIT's
realized statement or proof step is bypassed. All existing public imports remain verbatim.
The earlier restriction-presentation candidate was never delivered; it is retained only
in the sandbox scratchpad and is not an additional node or hole in this packet.

## Where the brief, the DAG or earlier work was wrong

The original plan suppresses the open-subspace/object-cohomology identifications and
normalization equations needed to instantiate the general continuity theorem. Those
identifications remain real work in both elementwise specialization proofs. The new
statements explicitly use the canonical existing diagram and cocone, preventing an
unjustified replacement by isomorphic groups with unidentified maps.

A previous full-presentation candidate compiled once, but repeated checking exposed
expensive kernel conversions through sheafification, inverse-image adjunctions, Ext,
and nested existential presentation data. Instance caches, smaller data structures,
and irreducible definition APIs were investigated without a reliably compiling complete
packet. None of those experimental API changes is delivered. The final reduction uses
the independent lifting and vanishing results, as in the existing general continuity
proof, and combines them directly in the category of abelian groups.

## New nodes

`lem-weil-pbc-punctured-neighborhood-cohomology-class-lift` is the class-lifting half
of Stacks 0A3D(2), via 0A37. Its proof plan constructs the spectral inverse limit and
restriction system and applies the existing general class-lifting declaration, with
open-cohomology and normalized canonical-map identifications.

`lem-weil-pbc-punctured-neighborhood-cohomology-eventual-zero` is the distinct
vanishing-after-shrinking half of the same argument. Its proof plan uses the existing
general eventual-zero declaration on that restriction system and explicitly identifies
the transition map with the original neighborhood diagram.

Change record: `coord/changes/T7-punctured-neighborhood-elementwise-continuity.md`.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
