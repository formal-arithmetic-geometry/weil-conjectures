## What changed

Replaced the proof of
`WeilConjectures.CompletedOpenTensor.completedOpenTensorContext` without changing
its statement or its public imports. Its private helpers prove invertibility of
the actual open-extension adjunction unit for independent coefficient and site
universes, and retain the defining restriction equation of the complete open
comparison. The context is then assembled from normalized completion realizations,
the all-input semilinear open model, and restriction descent for the same operations.

Added `Sheaf.Paper.CanonicalIntegralCompletionModels`, which constructs the ordinary
and derived completion models from a calculus whose integral closed structure is
fixed in advance. Added `Sheaf.Paper.CanonicalIntegralEvaluationCalculus`, isolating
only the one-scheme normalization of that calculus. All imports used only by proofs
are private imports. No existing dependency module, definition, public signature,
attribute, or instance was changed. The unit route is unchanged.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.CompletedOpenTensor.completedOpenTensorContext`
(node `lem-pur-completed-open-tensor-context`). The item now has zero holes.
Also proved `WeilConjectures.canonicalIntegralCompletionModels`
(node `lem-pur-canonical-integral-completion-models`) and all private helpers.

Added one hole:
`WeilConjectures.canonicalIntegralEvaluationCalculus`
(node `lem-pur-canonical-integral-evaluation-calculus`). Its statement concerns
one scheme and only the coherent calculus and its integral closed structure. It
has no open immersion, completion models, completion/unit comparisons, strict
open comparison, or restriction/completion comparison. Those remaining context
fields are constructed and their equations proved in this delivery. Its docstring
and node give the normalization argument, including the representative and
composition checks that an abstract left-adjoint comparison alone would not supply.

This is a decomposition: one original hole closed and one strictly smaller hole
added, net zero. No claim is made that the target closure is axiom-free. No hole
occurs in a definition or private declaration.

Remote compilation of the complete sandbox succeeded in import order:
`CanonicalIntegralEvaluationCalculus` (4.2 s),
`CanonicalIntegralCompletionModels` (5.8 s), and
`CompletedOpenTensorContext` (53.7 s). Each is below the 60 s limit.

## No longer needed

No original public import was removed and no module is withdrawn. The route does
not use `Sheaf.SixFunctors.OpenQuotientKoszulCompleteness` or its open-completeness
package to obtain coefficient data; it uses the already proved
`PrincipalKoszulStrictReplacement.coefficient_datum` directly. That larger
open-completeness assertion is unnecessary for this step, not declared globally
unused.

The existing `CompletionUnit.canonicalModels` existential is not used wholesale:
its ordinary/derived-model construction is reused with the prescribed integral
calculus instead. The general coefficient-calculus and closed-tensor comparison
nodes remain dependencies of the new normalization step. The original context's
complete-open comparison dependency is retained, with its construction repeated
privately to retain the required defining equation. No other original dependency
is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The existing canonical completion-model theorem chooses a coherent calculus but
does not assert that its integral closed structure equals
`IntegralOnSlice.duality.closed`. A natural isomorphism between tensor functors
does not prove that record equality. The new normalization statement isolates
this actual missing step rather than assuming it in context assembly.

The existing complete-open comparison theorem returns only `Nonempty`; that
existential forgets which restriction comparison was used. Its inverse-unit
construction does supply the required equation, and the private helper retains
it explicitly. Similarly, the open unit here must be the unit of the actual
normalized adjunction, and the proof uses its summand formula and derived
localization formula. It does not substitute an arbitrary adjunction or identify
independent universes.

No target statement is changed or disputed. No changes to other existing modules
or forced adaptations were necessary.

## New nodes

`lem-pur-canonical-integral-evaluation-calculus` records the remaining one-scheme
presentation-normalization step, in
`Sheaf.Paper.CanonicalIntegralEvaluationCalculus`. It fixes the integral closed
structure before choosing the rest of the coherent coefficient calculus. The
source proof uses normalized K-flat tensor presentations, evaluation and
transpose identities, and the triple-representative composition calculation.

`lem-pur-canonical-integral-completion-models` records the proved completion-model
assembly in `Sheaf.Paper.CanonicalIntegralCompletionModels`. It maps the global
unit to residue fields, uses the ordinary adjunction and derived-adjunction
comparison, and fills the completion-model record with the canonical termwise
limit comparison and constant-limit unit. It preserves the prescribed closed
structure literally. No change records are required: only this item's proof and
node, plus new modules and their nodes, are changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CanonicalIntegralCompletionModels": "161fa9ab5f8e7c01684290b480307f3004f953df", "Sheaf.Paper.CanonicalIntegralEvaluationCalculus": "ec95fa13a316bf64d6e86abaec3fb463419e3063", "Sheaf.Paper.CompletedOpenTensorContext": "bdee846c2311982b9557a4fb3d834467074d6f93"}, "results": {"Sheaf.Paper.CompletedOpenTensorRepresentatives": {"hash": "0e9b68cc2104d02715a6f702d027d56c076d6bfd", "status": "OK"}}, "seconds": 279, "time": "2026-10-27T23:42:49+0800", "transitive": 0, "version": 1}
```

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
