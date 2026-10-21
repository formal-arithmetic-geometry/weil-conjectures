## What changed

Filled the two remaining proof bodies in `Sheaf.Paper.DerivedInternalHomFilteredColimit`.
The restriction identity uses the declared normalized strict scalar-chain identification,
the single-complex tensor isomorphism, the normalization of both comparisons, and
naturality of the resolution unit. The quasi-isomorphism argument uses exactness of
finite-free tensor and filtered colimits, the ordinary scalar adjunction, preservation
of K-injectives by its exact right adjoint, and two-out-of-three. Existing signatures,
definitions, public imports, and the unit route are preserved. Private proof imports
reuse compiled private helpers from the strict data, finite-free stage, and continuity
modules. The added proof imports supply the normalized scalar-chain identification,
exact tensor colimits, preservation of K-injectives and the Hom quasi-isomorphism lemma.
The node proof and dependencies follow this direct argument.
The same declared scalar-chain theorem now supplies comparison existence, uniqueness
and naturality. This removes the duplicate private construction of those maps, while
keeping every public declaration and public definition body unchanged.

Change record: `coord/changes/X6-derived-internal-hom-proof-local.md` documents
the proof-local commands and removal of private implementation helpers requested
by the static preflight. All existing public signatures and definition bodies stay verbatim.

## Proved and sorry left

Closed the original holes in
`WeilConjectures.SfbHomFilteredColimit.scalarComparison_restriction` and
`WeilConjectures.SfbHomFilteredColimit.scalarComparison_quasiIso`.
Both realize `lem-sfb-dc-hom-filtered-colimit`. The item has zero `sorry` left and
this delivery adds zero holes. No statements are split off. The proof still uses the
existing declared scalar-chain identification; its proof is a separate existing item.

## No longer needed

No original import was removed. The obsolete private scalar-Hom section construction,
its degreewise differential proof, and its private naturality/extensionality helpers
were removed after replacing their uses with the declared strict scalar-chain API.

The direct strict square avoids `lem-sfb-ind-finite-free-scalar-model`
(`Sheaf.Algebra.Homology.IndFiniteFreeScalarModel`),
`lem-sfb-hom-flat-evaluation-roof`
(`Sheaf.Algebra.Homology.FlatInternalHomEvaluationRoof`),
`lem-sfb-hom-kflat-chain-transpose`
(`Sheaf.Algebra.Homology.OneKFlatChainTranspose`), and
`lem-sfb-dc-hom-scalar-adjunction`
(`Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`) as dependencies of this node.
The full ordinary-to-derived scalar model is unnecessary for proving this existing
representative statement: exact E and exact conservative restriction suffice.
The abstract derived category and existing representative definitions remain in use.
These modules and their other consumers are untouched; this is pruning of this node's
proof route, not withdrawal of the declarations.

## Where the brief, the DAG or earlier work was wrong

No statement was disputed or weakened. The old plan's derived roof detour can be
replaced by the normalized chain square already provided by the scalar-chain node.
The two scalar-extension presentations require explicit object and map equality
bridges; relying on broad definitional unfolding caused elaboration timeouts.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
