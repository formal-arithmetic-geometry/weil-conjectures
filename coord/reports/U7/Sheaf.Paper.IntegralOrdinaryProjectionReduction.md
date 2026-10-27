## What changed

Replaced the hole in `Sheaf.Paper.IntegralOrdinaryProjectionReduction` by a proof
from the existing finite-ring constructible-origin theorem, integral residue Tor,
intrinsic Tor transport, the adopted finite-coefficient pro-etale projection theorem,
and one new arrow-normalization statement. The statement of
`WeilConjectures.integralOrdinaryProjection_finiteReductions` is unchanged.

The proved private helpers `fixed_constructible` and `fixed_tor` transport the
finite reductions through the specified constant-scalar derived equivalence.
Constructibility uses the actual etale origin supplied by the existing essential-image
theorem, not a new chosen realization. The geometric base-field characteristic argument
proves invertibility of l in the residue fields. The final argument applies the
finite projection theorem and transfers invertibility across the arrow isomorphism.
No separated structure morphism or discrete integral etale origin is introduced.
Further proved private lemmas package the finite projection application and generic
isomorphism operations. They keep the coefficient-quotient specialization literal,
so the kernel checks small proof terms instead of unfolding the whole composite.

Added `Sheaf.Paper.IntegralOrdinaryProjectionArrowComparison`, containing only the
remaining comparison of the specified ordinary reduced arrow with the realized
fixed-scalar finite arrow. It is stated on arbitrary unbounded inputs and asserts
no invertibility. Its docstring and node give the proper scalar, counit, open-unit,
and constant-scalar realization argument. No shared definition or interface changes.

Final validation: both clean files compiled through `lcompile.py`: the new
comparison module in 53.6 seconds, the item in 6.3 seconds. All diagnostic options
were removed. Explicit local instance bindings are retained: replacing them with
ordinary bindings caused kernel normalization to exceed the file limit. The four
affected declarations have a scoped exception to `linter.style.haveILetI` documenting
why its style recommendation cannot be followed here.

## Proved and sorry left

Closed the original hole of
`WeilConjectures.integralOrdinaryProjection_finiteReductions`
(node `lem-sf-ordinary-projection-finite-reductions`).

Added one hole:
`WeilConjectures.integralOrdinaryProjection_reduction_arrowComparison`
(node `lem-sf-ordinary-projection-reduction-arrow-comparison`).

This is a decomposition: one original hole closed, one normalization hole added,
net zero holes removed. The finite constructibility, Tor-amplitude and projection
invertibility argument is proved; compatibility of the actual ordinary arrow with
finite coefficient realization remains. No holes remain in the item module.

The new statement is a genuine map-comparison step: it asserts an isomorphism of
arrows without claiming either arrow invertible, and has no constructibility or
finite-field assumptions. The finite projection theorem and the input hypotheses
are separately used by the proved parent. Empty schemes, zero objects, the residue
quotient and identity opens satisfy the same normalization and no exclusion of
these cases appears in the new statement.

## No longer needed

No original imports were removed and no existing module is withdrawn.

The parent no longer directly needs `lem-sf-proetale-constructible-origin`
(`Sheaf.Paper.ProEtaleConstructibleOrigin`): the more general existing
`lem-weil-pbc-finite-ring-constructible-derived-origin` supplies the actual origin.
It also no longer needs `lem-sf-comparison-tor-amplitude`
(`Sheaf.Paper.ComparisonTorAmplitude`): intrinsic realization Tor transport takes
the interval directly to the fixed-scalar category used by the adopted theorem.

The broad aggregate proof dependencies `lem-fix-operation-reduction` and
`lem-pur-compact-support-integral-coefficient-comparison` are replaced in the parent
by the explicit arrow-comparison step. That step records the precise perfect scalar
projection and proper/open normalization subresults it needs. The coefficient data
and projection definitions remain statement dependencies. The finite compact-support
projection formula and integral residue Tor are retained. These dependency changes
do not claim that the removed aggregate modules leave all other targets' closures.

## Where the brief, the DAG or earlier work was wrong

The planned aggregate coefficient-change theorem has separatedness assumptions on
both structure maps, while the item does not. The supplied-operation proper projection
and projection-reduction theorems concern completed operation-domain maps rather
than the ordinary completed-ring-sheaf arrow here. They cannot simply be applied to
this item. The new normalization statement isolates the missing comparison without
adding those hypotheses. The finite part uses the published generic projection
formula, which has precisely the needed domain and no such separatedness premise.

## New nodes

`lem-sf-ordinary-projection-reduction-arrow-comparison` records the comparison of
the reduced ordinary proper/open projection with the constant-scalar realization of
the finite projection on arbitrary complexes. Its source is the canonical-map
reduction paragraph of sk-thm-sf-pf-adic and the integral clause of
sk-thm-sf-pf-proetale. Its planned proof uses the perfect quotient for the proper
scalar comparison, the proper counit and open-unit squares, and finite scalar
realization. The parent now contains the complete finite invertibility argument.
No change record is needed: existing statements, definitions and public imports
are unchanged; the new statement is in its own module.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
