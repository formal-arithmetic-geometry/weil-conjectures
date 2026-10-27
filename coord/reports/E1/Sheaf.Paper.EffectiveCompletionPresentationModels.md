## What changed

Correct the false finite-evaluation-only presentation quantifier in
`WeilConjectures.effectiveCompletionPresentationModels`: require the existing
`IsIntegralComparisonPresentationCoherent` condition, as the published strict
completion realization already does. Correct the identical parent predicate
`IsEffectiveComparisonCompletionNormalized` in
`Sheaf.Paper.EffectiveComparisonRealizationModels` in the same packet.
This is an explicit auxiliary statement/definition repair, not a proof of the
old assertion. No target, coefficient object or actual operation changes.

Prove the repaired theorem by choosing canonical ordinary/derived models,
using the existing private normalized inverse Roos model, and applying
`strictQuotientCompletionRealization` directly. For a coherent presentation,
transport `trfStrictQuotientConeAugmentation` through the inverse strict tower
isomorphism. The existing inverse component identification, section-cast
cancellation and diagonal Roos coordinate formula give the requested sections
and zero shifted coordinate. Cancel the forward tower isomorphism in the
derived category and apply `strictQuotientCompletionUnit` for the last equality.
No extra theorem or arbitrary existence witness is introduced.

The parent model-existence proof consumes the repaired theorem verbatim.
A paired compile of the corrected item with the original parent produced the
expected error at `completion_normalization := hn`: `hn` requires whole-system
coherence but the old predicate does not. The parent definition repair fixes
that mismatch.
The private `completion_normalized` helper in
`Sheaf.Paper.PodCounitScalarWordCoordinates` must transport whole-system coherence
along the unique adjunction comparison as well as the old finite equations.
Its public theorem signatures and visibility stay identical.

Change record: `coord/changes/E1-effective-completion-presentation-coherence.md`.
The record lists every downstream module and the precise old/new interfaces.

## Proved and sorry left

The assigned source had one sorry:
`WeilConjectures.effectiveCompletionPresentationModels`
(`lem-trf-effective-completion-presentation-models`). Its OLD universal statement
is false and is not counted as proved. The corrected coherent-presentation
statement has a complete proof. This is a statement repair with proof, not
one unchanged-statement hole proved, nor a decomposition. Unchanged-statement
holes proved: 0; corrected statements proved: 1; holes added: 0; holes left: 0.

No new sorry statements are introduced. The three Lean source files in this
packet contain zero `sorry` tokens. The corrected item compiled with no warnings
in 29.8 seconds. The combined compile accepted the item, repaired parent,
adapted private consumer,
and all three unchanged direct importers. Profiling recorded 14.1 seconds of tactic
execution, 9.93 seconds of kernel type checking, and 425 milliseconds of artifact
serialization for the item. The service enforces its 60-second Lean acceptance
limit separately from wrapper/cache time. Profiling options and the three
validation-only source copies were removed before delivery. No axiom,
noncomputable arbitrary witness from an
unproved existence theorem, or hole in a definition is added.

## No longer needed

No original import is removed. No module is withdrawn and no source-library
declaration is removed. No globally unreachable module is claimed.

The old direct proof dependency
`lem-trf-isomorphism-multiplication-cone-descent` is unnecessary for this proof:
`strictQuotientCompletionRealization` supplies exactly the required completion
normalization, without applying the larger isomorphism theorem to the identity
scheme map or deriving stalk units. Its replacement dependency is
`lem-trf-strict-quotient-completion-realization`. The multiplication-cone module
remains a transitive import of the existing strict-unit/augmentation modules;
this packet does not claim to prune it from the global import closure.
All other original proof dependencies are retained for their actual used APIs.
The cast-cancellation helper also records the existing
`lem-trf-coherent-primitive-reduction-presentation` dependency. No blueprint unit
statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED in the original assertion: finite derived evaluations are
conservative on objects but not faithful on morphisms. They do not pin the
presentation isomorphism e. The same invisible-twist counterexample already
reviewed in `P4-strict-completion-presentation-coherence.md` applies here:
for A = Z_p, take B the completed countable free A-module, D = product_i A,
embed B by b_i -> p^i b_i, and put M = coker(B -> D). The nonzero class x of
(p^i)_i lies in every p^n M. The square-zero map delta on A direct-sum M
sending 1 to x reduces to zero at every finite derived level, while the
whole derived completion detects it because M is derived complete.
The automorphism 1+delta therefore twists e without changing kappa or the
old presentation equations. The requested section formulas and zero shifted
coordinate fix v, so the two proposed unit equations would force that twist
to disappear. This is the prior reviewed mathematical obstruction, not a
Lean-certified counterexample. The change record gives the complete argument.

The old proof sketch applied `TrfCompletionRoosNormalized` without its
already-required coherence premise. The corrected theorem and parent predicate
use exactly that existing premise; canonical coherent presentations exist for
every good complex by `coherentPrimitiveReductionPresentation`. The zero complex,
empty scheme and exponent-one quotient introduce no additional hypotheses.
The corrected nodes record the statement change and audit all DAG citers.
The current blueprint unit's route is retained, and no target-statement
meaning depends on the changed proof-interface predicates.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
