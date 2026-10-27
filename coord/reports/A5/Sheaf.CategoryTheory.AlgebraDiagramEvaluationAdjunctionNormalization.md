## What changed

Prove `CategoryTheory.AlgebraDiagramAdjunctionPresentation.evaluationAdjunctionNormalization`
by constructing ordinary comparisons, constructing the normalized right-derived
comparisons, proving varying-ring evaluation acyclicity by exact conservative scalar
restriction, and applying the counit, transpose, coefficient-cube and transition equations.
The ordinary construction and the coherence of already constructed derived comparisons
are stated in separate modules; both are proved in this packet. Generic normalized
right-derived square existence and uniqueness is proved in `AlgebraDiagramComparisonTools`.

The concrete interface is moved to a publicly reexported definition module so the
ordinary and derived results can refer to it without a cycle. The original theorem
signature and all normalization clauses are preserved. Constant rings and total
restriction functors use ordinary definitions with the same values. Cached canonical
abelian properties, explicit constant-slice localization bindings, and local opacity
avoid repeated unfolding of sheafification choices during elaboration. The new
coherence helper explicitly binds constant-evaluation exactness, supplied by the
existing interface theorems in the main proof. The revised definition module compiles using cached canonical instances.
The original baseline also compiled, with elaboration taking about 47 seconds.
See `coord/changes/algebra-diagram-concrete-definitions.md`.

Repair of return C-98383: the shared ordinary-comparison module was independently
created by M4 after the old delivery base. That current file and its original DAG
node are preserved unchanged. The evaluation-comparison construction instead lives
in `AlgebraDiagramEvaluationOrdinaryComparisons`, with the distinct node
`lem-pur-algebra-diagram-normalized-ordinary-comparisons`. Derived coherence imports
that evaluation module; the packet has no dependency on M4's unrelated restriction
comparison module. This resolves both file-name and node-id collisions.
The evaluation module reuses cached canonical instances and keeps the constant ring
locally irreducible in its presentation-specific proofs. The delivery tool rebases
the reconciled packet on current `sheaf-dag`.

## Proved and sorry left

Original hole: `CategoryTheory.AlgebraDiagramAdjunctionPresentation.evaluationAdjunctionNormalization`.
Closed: that declaration (one original hole). Added holes: zero. Remaining holes: zero.
The separate ordinary and derived coherence results are proved, rather than left as
unproved reductions. The reconciled full packet compiled without warnings: evaluation comparisons took
59.4 seconds, derived coherence 58.1 seconds, and the main theorem 21.2 seconds;
its reported unused section variable has been explicitly omitted. New public proved declarations include
`CategoryTheory.AlgebraDiagramAdjunctionPresentation.ordinaryComparisons_exists`,
`CategoryTheory.AlgebraDiagramAdjunctionPresentation.derivedComparisonCoherence`,
`CategoryTheory.algebraDiagramNormalizedDerivedSquare`,
`CategoryTheory.cartesianModulePullbackUnderlying`, and
`CategoryTheory.ExactDerivedSquare.normalized_naturality`.

## No longer needed

The unused private ordinary-and-derived restriction wrapper and its redundant
explicit `ShortExactPullback` import were removed from the new comparison-tools module;
the necessary public import remains in the interface. No existing module is withdrawn. The unfinished DAG parents still require this item.
The proof uses unit-normalized derived squares and exact conservativity in place of
choosing three resolutions and a homotopy equivalence between them. Consequently the
original direct proof dependencies `lem-sf-kinjective-derived-map-computation` and
`lem-weil-pbc-kinjective-hom-derived` are not direct dependencies of the main node.
K-injective representative and derived-map tools remain used inside the generic
coherence helper and are not withdrawn. The ringed-topos derived-composition result
remains needed by coefficient acyclicity. The original interface's public imports
are retained, as is the unit route. No source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. Empty diagrams make the vertex and arrow clauses vacuous;
loops and parallel arrows use their actual structural maps. The proof does not use
nonzero coefficient rings or flat coefficient changes. Varying-ring evaluation is not asserted to preserve
K-injectives. The proof instead proves acyclicity for the particular level direct
image by combining total coefficient restriction, constant evaluation, vertex
restriction and conservativity. Derived forgetful functors are not assumed faithful.
Ordinary forgetful faithfulness proves the ordinary cube and transition identities;
right-derived unit uniqueness transports those identities.

The earlier scratch report described a record replacement and claimed compilation
of the complete assembly prematurely. This packet retains the existential assertion;
the change record now describes the actual interface refactor and instance changes.

## New nodes

`def-pur-algebra-diagram-normalization-interface` attaches the moved concrete interface.
`lem-pur-algebra-diagram-normalized-derived-square` supplies the proved normalized
derived-square existence and uniqueness theorem.
`lem-pur-algebra-diagram-normalized-ordinary-comparisons` constructs the ordinary comparisons and
normalizes their inverse-image mate.
`lem-pur-algebra-diagram-derived-comparison-coherence` proves coherence of the already
constructed derived comparisons.
`lem-pur-cartesian-module-pullback-underlying` constructs the normalized underlying
geometric inverse image, used in the ordinary mate proof.
`lem-pur-derived-square-normalization-naturality` proves naturality of normalized
derived squares, used for the coefficient cube and transitions.

Change record: `coord/changes/algebra-diagram-concrete-definitions.md`.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
