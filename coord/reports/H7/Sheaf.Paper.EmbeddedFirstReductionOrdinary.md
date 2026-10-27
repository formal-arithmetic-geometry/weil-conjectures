## What changed

Filled `AlgebraicGeometry.ProEtale.IntegralModelsEmbedded.embeddedFirstReductionOrdinary`
with an ordinary scalar-extension argument. The specified finite scalar map is invertible,
and naturality of the constant-function map gives the actual reduction square. On the
coefficient-sized small site, the completion diagram gives sectionwise surjectivity of the
constant quotient, and the proved residue-sections helper supplies both principal kernels.
`ConstantCompletion.quotientTensorIso_exists` then supplies the ordinary common-quotient
comparison. The private `smallExtensionIso` transports scalar extension through the
small-module equivalence by taking mates of the existing restriction comparison. Full faithfulness
reflects the resulting natural isomorphism, and scalar-extension composition gives exactly
the original parenthesized functor expression.

The private `quotient_section_data` proves the section arguments over general ring sheaves
before specializing the actual maps, avoiding repeated unfolding of the coefficient ring
objects. `smallQuotientComparisonIso` transports the finite scalar isomorphism through this
comparison, and `first_reduction_square` proves the actual square by naturality.

Added only proof imports and private proved helpers; the public statement, definitions,
public imports, and unit route are unchanged. Updated the item's DAG proof and dependencies
for this argument. No source-library module is edited.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.IntegralModelsEmbedded.embeddedFirstReductionOrdinary`
(node `lem-sfb-embedded-first-reduction-ordinary`). Added zero holes and zero new nodes.
The item contains zero `sorry` statements. This is a proof from the existing declarations,
including the existing unproved `integralModelsEmbeddedCompletionDiagram` and
`ConstantCompletion.flat_and_quotients`; it does not claim that the entire transitive axiom
closure is now free of `sorryAx`.

Verification: the complete file compiled through `lcompile.py` in 28.8 seconds. Profiling
options were then removed; the delivery command checks the final file again.

## No longer needed

No original import was removed: `EmbeddedFiniteCoefficientRealization` is required by the
statement. The planned direct use of `lem-weil-pbc-ordinary-common-quotient-tower` is replaced
by the already proved, ordinary `ConstantCompletion.quotientTensorIso_exists`, so the item's
DAG no longer has that direct proof edge. The tower module is still a transitive dependency
of `ConstantCompletionEquivalence`; no global module withdrawal or closure pruning is claimed.
No new resolution, K-flatness, derived category, or quotient-tower statement is needed.

## Where the brief, the DAG or earlier work was wrong

The DAG's full ordinary tower construction is unnecessary for this single quotient.
The existing common-quotient tensor adjunction and equivalence transport suffice. No
mathematical statement was corrected or weakened. Empty site objects, zero modules, and
zero coefficient rings require no exceptions: all maps arise from equivalences and ordinary
adjunctions, and the section-kernel argument uses the supplied quotient presentation.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
