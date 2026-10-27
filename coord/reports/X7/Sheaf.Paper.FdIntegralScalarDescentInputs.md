## What changed

Replaced the proof hole in `WeilConjectures.fdIntegralScalarDescentInputs` with a
reduction that constructs its ordinary transports, ambient comparisons and integral
comparison family. A proved private helper lifts the ambient isomorphism through
fully faithful right whiskering by the integral inclusion. Its component equation
is retained as HEq, including the stage identity endpoint transports.

Choice is used only for the normalized comparison theorem: ordinary.generators
determines the sheafified tensor comparison, and the representative equation
determines the ambient natural transformation by descent from good representatives.
The other fields of the transport are proofs. The restricted isomorphism is the
fully faithful preimage of this fixed ambient isomorphism.

The proof establishes exactness of each supplied integral identity functor using
its specified shift normalization and reflection of distinguished triangles. It
also proves the good-representative lift by equality elimination at the two
endpoints. Finally it derives the requested inverse cocycle and inverse unit law
from forward equations, cancelling the actual comparison isomorphisms.

Two new theorem modules isolate the remaining presentation-transport arguments:
`Sheaf.Paper.FdIntegralScalarRestrictionExact` concerns the prescribed shift
squares and exactness of the scalar composites;
`Sheaf.Paper.FdIntegralScalarPresentationForward` concerns the forward associator
and multiplication/completeness unit equations. They assume an already constructed,
representative-normalized comparison; neither asserts its existence or repackages
the full item. Their docstrings and nodes give the complete intended arguments.

Another new module names the repeated representative equation as the real
proposition `fdIntegralScalarLiftProperty`; its body is that exact equation, with
no postponed proof or chosen data. This avoids repeating the large expression
in both lower theorem signatures.

Two proved modules separate the ambient proof-parameter normalization and the
exactness of the supplied integral stage functor. This keeps expensive coefficient
conversions out of the main construction. Neither adds a proof hole.

The existing theorem signature, definitions, instances, public imports and source
library files are unchanged. The item's node now follows the implemented route.
The intrinsic integral triangulation node
`lem-weil-integral-constructible-triangulated` is used as a generic tool for its
exact full inclusion; it does not replace any step of the trace-function unit.

Validation: the five helper modules compiled in import order. The complete item
passed its individual compiler check in 44.4 seconds. Development profiling options
were removed for delivery. The existing theorem signature was compared verbatim
with the shared source and is unchanged.

## Proved and sorry left

Closed the original hole in `WeilConjectures.fdIntegralScalarDescentInputs`
(`lem-fd-integral-scalar-descent-inputs`) conditionally on the two named transport
steps. There are zero holes left in the item module.

Added two holes, each the entire proof of a public theorem in its own new module:

- `WeilConjectures.fdIntegralScalarRestrictionExact`
  (`lem-fd-integral-scalar-restriction-exact`).
- `WeilConjectures.fdIntegralScalarPresentationForward`
  (`lem-fd-integral-scalar-presentation-forward`).

This is a decomposition: one original hole closed and two lower holes added.
The textual hole total increases by one; the project ledger determines the effect
in the targets' import closure. It is not a claim of an axiom-free proof. The private
restriction, shift-transport, HEq-composition and inverse-cancellation helpers are
fully proved.

The new statements were checked on identity inclusions, repeated fields, and the
zero object. They impose no strict inclusion or nonzero-object hypothesis. The
forward unit explicitly retains ordinary multiplication and the framework unit,
rather than replacing either by an identity.

## No longer needed

Removed the item's private import of
`Sheaf.Paper.FdNormalizedIntegralCompletionComparison`: the ambient existence and
normalization are obtained directly from
`Sheaf.Paper.FdCoefficientScalarLiftNormalization`. The normalized comparison node
is still needed by the new shift-transport obligation; it is not globally pruned.

Removed the item's private import of
`Sheaf.Paper.FdIntegralInverseScalarCocycle`: the main proof uses the new forward
presentation-transport statement and performs inversion itself. The inverse-scalar
module, scalar completion associator, integral pullback comparison realization and
PBC scalar extension remain dependencies of that forward transport argument.
No global module withdrawal or subtree pruning is claimed. All public imports
are retained.

## Where the brief, the DAG or earlier work was wrong

The stated lower results work in the ordinary/unrestricted completion presentation.
They do not directly provide the prescribed-shift or forward coherence statements
in the supplied PBC integral stage presentation. Those are substantive transport
steps, now isolated without moving the construction, representative lift or inverse
cancellation into another hole.

The latest trace-function blueprint file is a short definition without the older
coefficient-category paragraph referenced by the inherited node. The source
references here identify the extracted integral steps retained in the existing
node and its parent; no claim is made that the current short definition itself
contains these proofs. The unit's recorded realized route is unchanged.

## New nodes

`lem-fd-integral-scalar-restriction-exact` records the prescribed-shift transport
for an already normalized comparison and exact supplied stage identity functors.
Its only deferred mathematics is transfer of the actual normalized shift square
and scalar exactness through the coefficient presentation.

`lem-fd-integral-scalar-presentation-forward` records transport of the forward
completion associator and multiplication/completeness unit equations. The main
module proves inversion of these equations itself. Both nodes inherit the item's
chapter and unit, retain the same source comparison maps, and record actual
LeanSearch, Lean Finder and Mathlib grep searches. There are no change records
because no existing interface, definition or instance is changed.

`def-fd-integral-scalar-lift-property` names exactly the existing good-representative
lift proposition for an already supplied comparison. It adds no theorem or hole;
the two new theorem modules publicly import its owner.

`lem-fd-integral-ambient-scalar-normalization` proves the canonical target
presentation of the ambient normalization by proof irrelevance.

`lem-fd-integral-stage-exact` proves exactness of the supplied integral stage
equivalences by their prescribed shift normalization and fully faithful reflection.
Both are proved steps. Their statements import only the coefficient comparison
and finite-field datum owners, avoiding the unrelated common-stage calculus.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
