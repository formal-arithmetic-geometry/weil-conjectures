## What changed

Proved `WeilConjectures.sfCompactSupportProjection_transition` without changing its
statement, any definition, or any import. Apply the faithful functor forgetting
commutativity to reduce the claimed equality to compatibility of the inverse-limit
cone of `integralCoefficientSheafSystem`. Its adjacent-arrow cone equation is
`limit.w`; `Functor.ofOpSequence_map_homOfLE_succ` identifies the diagram map with
the specified quotient transition.

Validation: the assigned module compiled through `lcompile.py` in 7.5 seconds.
The proof works for every scheme and every natural index, including index zero;
it uses neither geometric finiteness nor a nonempty-scheme hypothesis.

## Proved and sorry left

Holes closed (1): `WeilConjectures.sfCompactSupportProjection_transition`.

Holes left (1): `WeilConjectures.sfIntegralCompactSupport_constructible`.
Its node is `lem-sf-integral-compact-support-constructible`. Its existing
statement, complete natural-language proof plan and DAG attachment are retained. This is a partial proof delivery of a module containing two holes.

Holes added: none. Split-off statements: none. No definition contains a new hole.

## No longer needed

None. No imports, declarations, modules, or nodes are withdrawn. The main theorem's
open-extension, finite constructibility and tower-comparison route is still needed;
proving the coefficient projection equation does not prune that route.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found in the assigned declarations.

The projection equation is already the cone condition of the recorded coefficient
limit; it needs no new comparison theorem or additional ring-sheaf construction.

For continuation on the main theorem: the current DAG dependencies
`IntegralOpenReduction.integralOpenReductionComparison` and
`CompactSupportProperImageTower.compactSupportProperImageTower` use the localized
slice extension (`IntegralOpenReduction.shriek` and `finiteExtension`) and
`IntegralOnSlice.IsComplete`. The assigned statement uses `IsSfDerivedComplete`,
`sfIntrinsicExtensionByZero`, and `sfCompactSupportTransition`. The tower theorem's
proper transition also uses finite-quotient restriction comparisons, whereas
`sfDirectImageTransition` conjugates the canonical integral reduction transition
by the completed-coefficient direct-image comparisons. These identifications have
to preserve the normalized units and transitions, not just identify the objects.
`sfDerivedComplete_iff_legacy` supplies the completeness-predicate comparison.
No alternate statement, extra hypothesis or unproved identification is introduced
in this packet.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
