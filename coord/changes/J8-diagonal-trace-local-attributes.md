# J8: ordinary tensor proof helpers for the diagonal geometric model

The only existing Lean module changed is the assigned item
`Sheaf.Paper.DiagonalTraceGeometricModelExistence` (holder J8).
Its public import and theorem signature stay verbatim. The new imports are private;
all added declarations in this existing module are private, proved helpers.

The proof opens `WeilConjectures` for existing tensor names and marks `lineModule`,
`adjointSection`, `evaluatedAdjoint`, `ordinaryAdjoint`,
`Scheme.proEtaleConstantRingComparison`, and `Scheme.proEtaleRingDirectImageMap`
locally irreducible. These attributes are local to this module and prevent costly
carrier unfolding during its section-normalization proof. They change no global
attributes, instances, definitions, public imports, or declaration signatures.
No downstream adaptation is needed because there is no imported interface change.

Three new modules provide the concrete tensor API and the two remaining
construction statements, each attached to a new DAG node. The item is proved
from these statements and the already proved generic mate theorem. This is a
decomposition, with one original hole closed and two strictly smaller holes added.
All four modules compiled remotely. The delivered item has no profiling options.

The first delivery preflight found that the tensor definition node recorded its
structure fields as part of `lean.statement`. The signature reader records only
the structure header, so that record now matches its output exactly. The complete
fields are unchanged in Lean and described by the node's mathematical statement.
