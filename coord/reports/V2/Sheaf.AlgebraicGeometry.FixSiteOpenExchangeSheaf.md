## What changed

Proved `AlgebraicGeometry.ProEtale.fixSiteOpenExchangeSheaf` in the assigned module.
The proof instantiates the existing proved `exchange_comparison` calculation with the
specified etale and pro-etale extension functors, pullbacks, comparison isomorphisms,
and open adjunctions. Its five inputs are the two comparison inverse-unit identities,
the pro-etale exchange inverse-unit identity, the upstream etale exchange unit identity,
and `fixSiteOpenExchangeSquare`.

The pro-etale unit formula initially caused a kernel timeout when Lean compared the
commutativity witness extracted from `IsPullback` with the witness of the supplied
square. An explicit equality between the two `upperStarCompIso` values rewrites that
formula before applying the generic calculation. This preserves every canonical map
and avoids expanding the conjugated exchange. No compile limit was raised.

The declaration signatures, definitions and docstrings are unchanged. The existing DAG
proof is the route implemented, so it needs no dependency or statement changes.
The retained module compiled cleanly before pruning in 12.7 seconds; delivery performs
the final compilation and declaration checks after the two unused imports are removed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.fixSiteOpenExchangeSheaf`
(node `lem-fix-site-open-exchange-sheaf`).

One of one holes proved; zero holes added or split off. No `sorry` remains in the
item module. Existing dependency declarations are used as supplied; this does not
claim that every transitive dependency has already been proved.

## No longer needed

Removed the unused private proof import
`Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`: this ordinary-sheaf
calculation uses the canonical weakly etale base-change map and its proved unit formula
directly, without constructing its derived lift. Removed the redundant private import
`Sheaf.AlgebraicGeometry.ChosenCartesianSquare`, already public through
`Sheaf.AlgebraicGeometry.OpenImmersionSquare`.

No node or declaration is withdrawn. All seven existing proof dependencies remain
mathematically relevant to the recorded route: the ordinary base-change construction,
comparison normalization, canonical pullback comparison and square coherence are used.
The redundant imports can remain needed by other modules; no global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The previously proved generic comparison lemma and
the specialized square theorem suffice to close the remaining hole, with an explicit
commutativity-witness rewrite to keep kernel checking small. The proof uses arbitrary
bottom maps and adds no condition excluding empty opens, identity squares or the zero ring.
No targets, definitions, other groups' modules, unit routes or source-library declarations
are changed. No new nodes or change records are needed.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
