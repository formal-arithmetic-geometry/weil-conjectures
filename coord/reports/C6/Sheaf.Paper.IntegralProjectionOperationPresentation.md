## What changed

Reduced `WeilConjectures.integralProjection_operationPresentation` to the proper
counit factor, `WeilConjectures.integralProperOperationProjection_isIso`, in the
new module `Sheaf.Paper.IntegralProperOperationProjection`.

The item now proves the open-factor and compact-support assembly itself. It
expands the operation projection into its proper counit component, proper image
of the supplied open isomorphism, compact-support identifications, and equality
transports. It constructs the source isomorphism from the support value equality,
the published qcqs realization, the datum's tensor normalization, common flat-term
K-flat representatives, constructible tensor completion, and the source completion
unit from `integralDomains`. The independently established concrete
`SfProEtaleProjection.integral_isIso` supplies invertibility of the other arrow.
For invertible arrows p and q and a source isomorphism e, the target isomorphism
is `p⁻¹ ≫ e ≫ q`; cancellation supplies the square for `Arrow.isoMk`.

The new lemma concerns only the proper right-adjoint projection component on
integral bounded constructible inputs. It has no compact-support projection,
ordinary tensor-model parameters, comparison of compact-support presentations,
or open-projection conclusion. Its source, proof in words, and DAG node describe
normalizing the proper adjunction and applying the independently available
proper case of the concrete projection formula. This is a genuine proper-factor
subproblem of the original node's second proof step.

The item statement, public imports, universes, and visibility are unchanged.
New proof imports are private. No other existing Lean module or definition is
changed, so there are no consumer adaptations or change records.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.integralProjection_operationPresentation`
(node `lem-sf-integral-projection-operation-presentation`).
The item module has zero remaining holes. The private helpers
`arrowIsoOfIsoSource`, `stageProjection_isIso`,
`dataProjection_isIso`, `operationProjection_isIso`, and `tensorPresentation` are proved.

Added exactly one hole:
`WeilConjectures.integralProperOperationProjection_isIso`, node
`lem-sf-integral-proper-operation-projection-isomorphism`, in
`Sheaf.Paper.IntegralProperOperationProjection`.

This is a decomposition: one original hole closed and one strictly smaller
proper-factor hole added, for zero net holes closed. The remaining theorem
proves neither the source comparison nor the open/compact-support assembly nor
the arrow-category construction; these are all implemented in the item.

Validation: `lcompile.py --all` compiled both delivered modules without warnings
and returned exit code zero under the unchanged 60-second acceptance limit.
The item signature and public imports match the shared source verbatim. Both
DAG Lean statements match their declarations and proof dependencies match the
union of proof-step uses. No profiling options remain.

## No longer needed

No existing Lean import is removed and no module is withdrawn. No module is
claimed globally unreachable.

The item no longer directly uses
`lem-tw-ordinary-completed-integral-pullback`
(`Sheaf.Paper.OrdinaryCompletedIntegralPullback`) or
`lem-fix-qcqs-completion-unit-locality`
(`Sheaf.Paper.QcqsCompletionUnitLocality`). The separate target comparison and
the canonical completion-unit extension equation in the original item proof
plan are unnecessary for its existential arrow-isomorphism conclusion. These
nodes remain dependencies of the concrete completed projection development;
the pullback comparison also remains a dependency of the new proper-factor
node. They are not globally pruned.

The revised item node instead records the proper-factor lemma, the concrete
pro-etale projection theorem, tensor completion, K-flat resolutions, and the
support constructions actually used by the Lean proof.

## Where the brief, the DAG or earlier work was wrong

The written theorem requires only `Nonempty` of an arrow isomorphism. It does
not prescribe either endpoint component. Its earlier proof plan establishes a
stronger canonical presentation square. The shorter argument uses independent
invertibility of the concrete completed map and an actual source isomorphism;
it does not need to establish that stronger square. No statement was weakened.

The general integral operation-stage projection theorem imports this item and
cannot be used here. The concrete pro-etale projection theorem is independent:
`import_direction.py may` confirms that its module does not reach the item.
The new proper-factor node only uses that independent proper case, not the
operation-stage theorem or any parent of this item.

The unit `sk-rem-sf-pf-done` has no realized steps to remove. Its use of the
pro-etale projection theorem is retained. The finite formula, reduction,
adic reconstruction and field-stage unit route is unchanged.

Searched both library roots for projection/presentation and proper-projection
results. Mathlib searches included leanfinder, Loogle, and grep. The closest
generic results transport projection mates through compatible tensor and
adjunction comparisons; they do not establish the remaining normalization of
the supplied integral proper adjunction. Existing integral proper results that
require separated structure maps cannot be applied to the present domain.

Edge cases: empty schemes and zero inputs use the same tensor presentations
and categorical cancellation. The supplied open projection is already an
isomorphism, including identity-open compactifications. The proper-factor
statement adds no separated structure morphism or finite-Tor hypothesis.

## New nodes

`lem-sf-integral-proper-operation-projection-isomorphism` records invertibility
of just the normalized proper counit component. Its statement is the proper
factor of the original plan, with arbitrary integral bounded constructible
inputs. Its proof normalizes tensor and pullback, transports the supplied
adjunction by uniqueness, and uses the independently established proper case
of the concrete projection formula. It does not repackage the original
compact-support arrow-isomorphism statement.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
