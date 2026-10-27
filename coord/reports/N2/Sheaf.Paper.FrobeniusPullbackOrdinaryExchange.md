## What changed

Filled `WeilConjectures.OrdinaryAutomorphismSquare.frobeniusPullbackOrdinaryExchange`
from the existing simultaneous automorphism comparison system, isomorphism-field
transport and invertibility of mates along equivalences. Its signature and all
existing public definition signatures are unchanged. The bodies of
`integralSquare` and `finiteSquare`
are expressed componentwise through `comparisonSquare` and
`functorComparisonSquare`; their proved equality lemmas identify them with the
original functor-level composites.
The change record is `coord/changes/ordinary-automorphism-integral-square.md`.
The consumer scan reports no downstream Lean modules. Added private helpers for
restriction
of equivalences, the component formula for mates, normalized compositors, finite
square pasting, and composite common-stage representative arrows. The normalized
square is identified componentwise. Large operation definitions remain closed
during the proof, with explicit conversion of their full-subcategory interfaces.

Added `Sheaf.Paper.AutomorphismSquareRationalScalar`: its theorem proves the raw
rational scalar equation from the integral scalar equation using the prescribed
object and pure-tensor formulas. Added
`Sheaf.Paper.IntegralComparisonCompositionReduction`: its theorem isolates the
finite-reduction normalization of the already prescribed whole-system compositor.
The main proof uses this result twice and proves the square reduction by actual
categorical pasting. All three new imports in the item are private proof imports.
Updated the item's proof steps and dependencies to match this argument.

The exact inverse transports use `IsomorphismFieldTransport` and therefore do not
require separatedness of X or Y over the coefficient base. The exchange proof
retains the supplied adjunction and closes its formula by expanding `mateEquiv`.
It applies to arbitrary supplied full domains closed under the stated operations.

## Proved and sorry left

Closed the item's one original hole:
`WeilConjectures.OrdinaryAutomorphismSquare.frobeniusPullbackOrdinaryExchange`.
Proved the new theorem `WeilConjectures.automorphismStageRationalSquare_scalar`.
There are no holes in either of those modules. The item compiled in 38.9 seconds
before removing two blank-line style warnings. The kernel no longer unfolds
functor-category equality transports for the integral and finite square components.

One new hole remains:
`WeilConjectures.integralComparisonComposition_reduction`, node
`lem-pod-integral-comparison-composition-reduction`. This is only the finite
reduction formula for a single completed compositor. It has no rationalization,
coefficient scalar equation, common-stage descent, exact inverse transports or
exchange assertion. Its source and complete proof in words are in its docstring
and node. Closing one original hole while adding this hole is a decomposition,
with net zero new hole closure, rather than a complete proof of the import closure.
No hollow definition, arbitrary existential witness construction or axiom is added.

## No longer needed

Removed the unused private proof import
`WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`: the proof uses the
supplied arbitrary adjunction directly. No existing module is withdrawn.
Public imports retained by the item's API are
not claimed as pruned. In particular `IntegralPullbackComposition` and its
existing declarations remain needed for the named family and reduction maps.

The proof does not apply `integralPullbackComposition`: that theorem chooses a
compositor satisfying finite reductions, whereas the item's additional
normalization fixes the compositor from S. The proof constructs precisely that
normalized family, and uses the new finite normalization node instead.

The separate scalar identity/tower proof through
`lem-pod-pullback-identities-scalar-extension` and
`lem-pur-integral-operations-scalar-extension` is replaced by the existing
simultaneous system's square scalar theorem. Their definitions and public imports
remain in use in the statement and this is no claim that their modules are
unreachable from other targets.

The original proof's restructuring of the Cartesian scheme square over k is
unnecessary. `ExchangeOnDomains` quantifies over the supplied ordinary adjunction
and explicitly defines the exchange to be its mate. Expanding that mate proves
its component formula directly. Thus the proof does not use the assertions of
`fix-prop-adjunctions` or `def-exchange-projection`; their statement dependencies
and supplied-domain public API remain unchanged. The mate-invertibility theorem
itself remains essential. Removed the obsolete top-level `tool_uses` entry
`fix-prop-adjunctions`; the other approvals retain their original order.

The direct `def-weil-rationalization-karoubi` proof dependency is handled inside
the new proved rational-scalar lemma, whose pure-tensor formulas use the existing
localization API. It remains a transitive dependency; its module is not withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan's appeal to the existential completed compositor is insufficient
to prove the item's equations identifying both compositor components with
`integralComparisonComposition S`. The existing normalization coherence gives
naturality, associativity and scalar compatibility, but does not state the exact
finite-evaluation equation with `integralPullbackReductionIso`. The new finite
normalization node records that genuinely separate missing comparison result.
Equality of maps is never inferred just from separately evaluated reductions.

The single simultaneous system is essential: independent existential choices for
each embedding E→L would not supply the one S preceding all E,L quantifiers in
the item. `automorphismConstructibleStage_comparison_system` supplies exactly
that simultaneous system. Its generic comparison constructors need no
separatedness of X or Y. The stronger separated-scheme equivalence theorems in
that module are not used.

The adopted source library is unchanged. The proof uses the generic comparison
API of `lem-sf-automorphism-constructible-stage-equivalence`, a node from another
unit, without bypassing any realized statement or proof step of `sk-lem-finite`.
Any approval bookkeeping for this tool use belongs to the independent reviewer;
no new top-level `tool_uses` approval is asserted in this packet.

## New nodes

`lem-pod-integral-comparison-composition-reduction`, module
`Sheaf.Paper.IntegralComparisonCompositionReduction`, records the finite
normalization equation for one compositor. It is needed twice in the item's
finite square pasting. The identity-map, empty-scheme, zero-object and n=0 cases
retain the same types and the exponent is n+1 throughout; the universal good
representative quantifiers match the actual rho definition.

`lem-pod-automorphism-square-rational-scalar`, module
`Sheaf.Paper.AutomorphismSquareRationalScalar`, records and proves localization
of the integral scalar square. It covers every rational object via its underlying
integral object and uses tensor coefficient one on localized integral arrows.
Identity coefficient extensions and zero objects need no special hypotheses.
Neither new node changes an existing statement. The definition performance repair
has change record `coord/changes/ordinary-automorphism-integral-square.md`.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
