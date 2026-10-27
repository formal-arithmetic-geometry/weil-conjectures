## What changed

Proved `AlgebraicGeometry.HilbertCoefficient.exists_regularHilbertCoefficientDatum`
in `Sheaf.AlgebraicGeometry.RegularHilbertCoefficientData` by specializing the existing
`exists_nonreduced_regularHilbertCoefficientDatum` theorem to the same closed immersion
and structure morphism. The latter already supplies exactly the required datum and
ordered vertices, together with additional positive-degree and zero-ideal conclusions.
The proof retains the vertices, specializes its universal quantifier to each Q, and
packages the supplied datum as Nonempty. The theorem signature and public imports are
unchanged. The proof import is private.

Updated only the item's node proof, proof_deps and proof_origin to describe this route.
No new declarations, nodes, definitions, statement changes, or consumer adaptations.
The item's unit has no realization of this node as its statement or proof steps, and
the unchanged local coefficient construction is used as a general tool; the unit's
statement and route remain intact. The replacement dependency belongs to
`sk-p-dl-a1-perverse`; its general coefficient existence theorem is used as a tool,
not its perverse-sheaf unit argument. Any tool-use approval belongs to the reviewer;
no maintainer-owned tool_uses field was edited. The replacement theorem does not depend on the
item: import_direction.py accepts the import, and a traversal of its statement/proof
DAG dependencies (1104 nodes) finds no path back to the item.

Verification: the final single file compiled cleanly through lcompile.py in 2.2 s
(exit code 0, no warnings). Its result file is
`/home/ubuntu/weil-launcher/compile-results/20a02acd03d7a6363ddc8d11.txt`. Edge cases are inherited directly: the vertices stay fixed before Q,
the empty family makes the Q condition vacuous, n=0 is allowed, and nonclosed points
use the identical RegularHilbertCoefficientDatum and Taylor ideal. No new existence
witness is chosen inside a definition.

Searches: leanfinder returned standard smooth/etale presentation material, not this
coefficient theorem; loogle for "HilbertSamuel" returned no hits; Mathlib grep returned
only unrelated coefficient/presentation material. Local rg found the existing stronger
arbitrary-ideal coefficient theorem, whose full declaration and proof node were read.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.HilbertCoefficient.exists_regularHilbertCoefficientDatum`
(node `lem-trf-regular-hilbert-coefficient-data`). There are zero sorry declarations
left in the item and zero holes added or split off by this delivery.

This is a proof from an already stated dependency, as required by stage 3, not a claim
that the complete coefficient theory is now axiom-free: the existing theorem
`AlgebraicGeometry.HilbertCoefficient.exists_nonreduced_regularHilbertCoefficientDatum`
(node `lem-per-nonreduced-regular-hilbert-coefficients`) still contains its existing sorry.
That theorem and its module were not modified.

## No longer needed

Removed the unused private imports `Mathlib.RingTheory.FiniteType`,
`Mathlib.RingTheory.Noetherian.Basic`, and
`Mathlib.Algebra.Module.FinitePresentation`.

The item no longer directly uses these eight planned proof dependencies:
- `lem-trf-block-straightening-projection-transport`
  (`Sheaf.AlgebraicGeometry.BlockStraighteningProjectionTransport`);
- `lem-trf-coefficient-locus-uniform-division`
  (`Sheaf.AlgebraicGeometry.CoefficientLocusUniformDivision`);
- `lem-trf-coefficient-order-hilbert-equality`
  (`Sheaf.AlgebraicGeometry.CoefficientOrderHilbertEquality`);
- `lem-trf-exact-block-coefficient-projection`
  (`Sheaf.AlgebraicGeometry.ExactBlockCoefficientProjection`);
- `lem-trf-extended-hilbert-local-upper-bound`
  (`Sheaf.AlgebraicGeometry.ExtendedHilbertLocalUpperBound`);
- `lem-trf-generic-monotone-diagram`
  (`Sheaf.AlgebraicGeometry.GenericMonotoneDiagram`);
- `lem-trf-homogeneous-continuous-formal-division`
  (`Sheaf.RingTheory.HomogeneousContinuousFormalDivision`);
- `lem-trf-jet-diagram-hilbert-control`
  (`Sheaf.AlgebraicGeometry.JetDiagramHilbertControl`).

They remain dependencies of the stronger theorem's construction and therefore are not
claimed as globally pruned modules. No module is withdrawn or pruned. No public import
is removed and no source-library declaration is changed.

## Where the brief, the DAG or earlier work was wrong

The old proof plan duplicated the existing arbitrary-ideal theorem's construction.
Its stronger conclusion specializes directly to this reduced case; reducedness does
not need to be used. The original theorem statement is preserved verbatim. No
mathematical error in that statement was found, and no tool failure occurred.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
