## What changed

Prove `AlgebraicGeometry.ProEtale.CondensedRing.Evaluation.contractible_sections_monoidal`
without changing its statement. The proof packages the existing ordinary tensor comparison,
descends an exact monoidal equivalence along the K-flat localization, identifies the tensor
model in the evaluation datum with the native tensor, and transports the composite through
the exact derived composition isomorphism. All added helpers are private and proved.
The original public imports remain; new imports are proof imports only. Update the existing
node's proof, proof dependencies and proof-origin note to describe this route.

## Proved and sorry left

Close the one original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.Evaluation.contractible_sections_monoidal`
(node `lem-zl-contractible-sections-monoidal`). No holes are added and no `sorry` remains
in the delivered Lean module. No new public statement, definition repair or split is used.

## No longer needed

`lem-sfb-ringed-equivalence-resolving-tensor-descent` and
`Sheaf.Algebra.Homology.RingedEquivalenceResolvingTensorDescent` are not needed by this proof:
the exact derived equivalence is made monoidal directly on the categorical K-flat
localization. This removes that planned dependency from this node only; no declaration or
module is withdrawn. Other consumers may still need it. Neither original public import is
removed. The exploratory proof import
`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable` was removed because
no dualizability theorem is used. The existing native-model identification is used as a tool because it directly
identifies the coefficient model present in the hypothesis with the fixed native tensor.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged and no mathematical error was found. The planned resolving-tensor
transfer is longer than necessary for this existence claim: ordinary monoidal equivalence,
K-flat monoidal localization, and the already proved native-model comparison suffice.
The arbitrary finite-limit and finite-colimit preservation witnesses are retained verbatim.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
