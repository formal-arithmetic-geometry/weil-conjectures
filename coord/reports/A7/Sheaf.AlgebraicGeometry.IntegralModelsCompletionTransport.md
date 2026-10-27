## What changed

Proved `AlgebraicGeometry.ProEtale.IntegralModelsStacks.completion_transport` from
ordinary flatness/quotient data and the local completeness comparison for the specified
completed realization. The original theorem signature and both public imports are unchanged.

The proof constructs the equivalence from internal modules to section module sheaves on
the coefficient-sized small site, localizes it termwise, and proves the restriction square
using the existing identity-on-sections scalar comparison. It applies
`flat_ringed_ideal_complete_equivalence` and
`siteDerivedRestrictScalars_locallyDerivedComplete_iff`, then restricts the ambient
presentation equivalences to the complete full subcategories. A proved categorical helper
transports the inclusion natural isomorphism back through the fully faithful discrete
presentation equivalence. The pointwise completeness equivalence uses the same square.

Two strictly smaller presentation obligations are stated in separate modules:
`IntegralModelsFlatResidue` concerns ordinary module flatness, finite type of the first
kernel, and equality of the first quotients; `IntegralModelsCompleteSectionPredicate`
compares only the completed realization's local predicate with the extended residue ideal.
Neither asserts an equivalence on complete categories or the original theorem.
Both have sources, complete proofs in words, and matching DAG nodes.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.completion_transport`
(node `lem-sfb-integral-models-completion-transport`). No sorry remains in the item module.

Added holes, each the entire proof of a public named theorem in its own module:

- `AlgebraicGeometry.ProEtale.IntegralModelsStacks.integralModels_flat_residue`
  (`lem-sfb-integral-models-flat-residue`, `IntegralModelsFlatResidue`).
- `AlgebraicGeometry.ProEtale.IntegralModelsStacks.integralModels_complete_section_predicate`
  (`lem-sfb-integral-models-complete-section-predicate`,
  `IntegralModelsCompleteSectionPredicate`).

Counts: one original hole reduced, two lower holes added; this is a decomposition,
not a net proof-progress claim. The categorical transport, exact restriction square,
representative comparison, and isomorphism invariance helpers are proved without holes.
No data is chosen from an unproved mere-existence theorem.

All three files compile through `lcompile.py`. The transport file takes 34 seconds after
marking `upperStarFromPoint` locally irreducible; no global definition or attribute changes.
The two new modules have only their documented named theorem holes.

## No longer needed

No original import is removed and no module is withdrawn. The unit's complete-object
restriction route is retained. The direct proof uses the general flat ringed-ideal
complete equivalence, rather than first passing to a quotient-tower completion unit;
the displayed predicates are already local internal-Hom predicates.

The item node no longer directly lists
`det-prop-sfb-qlbar-colimit-x-integral-limit`,
`det-prop-integral-criterion-constant-coefficients`,
`lem-weil-l-adic-extension-integers-dvr`, or
`lem-weil-pbc-constant-completion-equivalence` in its proof dependencies.
The integral limit, DVR, and general constant completion results remain needed below the
new ordinary comparison nodes; none is claimed globally pruned. The specialized
`integral_constant_completion` conjunction is not used: its local flatness and quotient
content is already available in the general `flat_and_quotients` API, and its reflector
and finite-reduction clauses are unnecessary for this local-predicate argument.

## Where the brief, the DAG or earlier work was wrong

The original plan conflates several non-definitional presentations: internal modules,
section module sheaves, the equivalent small site, and the completed realization's
coefficient ring. The existing constant completion theorem cannot be applied directly
to these internal coefficient types. This delivery makes the ordinary algebra comparison
and completed-predicate comparison explicit and proves the remaining transport.
No mathematical statement is disputed or weakened, and no target or unit route changes.

`IntegralModelsFlatResidue` is tested against the zero/empty-site case: the kernel can be
the zero ideal and the flatness/quotient assertions still hold. No nonzero or invertibility
assumption on a uniformizer section is introduced. The predicate comparison quantifies
over arbitrary complexes, including zero and unbounded complexes, and introduces no
constructibility or Tor hypothesis.

## New nodes

`lem-sfb-integral-models-flat-residue` realizes the ordinary coefficient algebra in unit
proof (1), using Stacks 093M/099L and the normalized integral coefficient limit. Its
conclusion is the hypotheses of the existing flat ringed-site equivalence, not an
assertion of a derived equivalence. Its source module is
`Sheaf.AlgebraicGeometry.IntegralModelsFlatResidue`.

`lem-sfb-integral-models-complete-section-predicate` realizes the completed side's
presentation comparison: identify the first kernel with the scalar-extended discrete
kernel and transport local Hom vanishing through the exact section and site equivalences.
Its source module is `Sheaf.AlgebraicGeometry.IntegralModelsCompleteSectionPredicate`.
The general flat ringed-ideal equivalence and internal scalar section comparison are
used as generic tools; they do not replace any step of the integral-models unit.
No interface change record is required: existing public signatures, definitions,
instances, attributes and public imports are unchanged; new public lemmas have new nodes.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
