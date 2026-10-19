## What changed

Proved the three existing theorems in
`Sheaf.AlgebraicGeometry.CompactSupportActionBaseChange` using the existing finite-torsion
compact-support exchange API. The Cartesian square is an immediate application of
`IsPullback.of_horiz_isIso`. The identity law uses `shriekBaseChange_id` and cancels the
identity-pullback comparisons. The main theorem combines exchange invertibility,
compactification-comparison naturality and the horizontal-pasting law.

The private coherence argument first compares the canonical exchange with the exchange for
any Cartesian compactification model. It proves horizontal pasting for the twice-pulled-back
model and transports that equation to arbitrary compactifications using `shriekIso_trans` and
naturality. Pasting in the two orders around the automorphism square, followed by naturality
at theta, gives exactly the required coefficient action equation.

Three generic constructions factor the existing exchange, action and pulled-back coefficient
isomorphism. Explicit equation lemmas provide their specialization API; the final proof uses
these equations instead of asking the kernel to unfold the whole concrete composite. They preserve the canonical maps and the existing signatures,
while avoiding expansion of derived resolutions during specialization. No arbitrary objects are chosen.
The change record is `coord/changes/compact-support-action-formal-constructions.md`.
The existing node's proof and dependency list follow this proof.
The retained final module compiled cleanly against the current server build in 5.1 s
with the project's standard options and limits. The resumed dry run also passed compilation
and stage-3 preflight (review class CODEX).
A diagnostic copy also compiled in 6.1 s with its heartbeat budget reduced to 10000.

## Proved and sorry left

Closed all 3 original theorem holes, all attached to
`lem-amb-compact-action-base-change`:

- `AlgebraicGeometry.Etale.compactSupportActionSquare`
- `AlgebraicGeometry.Etale.compactSupportAction_id`
- `AlgebraicGeometry.Etale.compactSupportActionBaseChange`

No `sorry` remains in the item, and no new hole or split-off theorem is added.
This proof uses the existing declarations of its stated dependencies; it does not assert
that all dependencies of those declarations are already free of `sorry`.

## No longer needed

Removed the unused proof imports `Sheaf.AlgebraicGeometry.CompactifiableOverField` and
`Sheaf.AlgebraicGeometry.DerivedCategories`. The latter is a retired re-export of the
already publicly imported `WeilConjectures.AlgebraicGeometry.DerivedCategories`.
The redundant direct proof import
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` is also unnecessary: the public
base-change import already supplies this definition and the proof uses the generic API.

Removed `lem-weil-pbc-finite-type-over-noetherian` from proof dependencies and the node's
top-level tool approvals: the generic coherence proof needs no Noetherianity assertion
about the fibre-product source. It uses the supplied compactification directly.
No compactification-existence theorem, field restriction or new geometric finiteness
argument is required. Other nodes may still need the pruned modules or lemma.
The existing finite-torsion base-change and canonical comparison imports remain: these
are the packages whose recorded identity, pasting and comparison declarations are used.

## Where the brief, the DAG or earlier work was wrong

The retained report described only two closed holes, whereas its Lean draft attempted all
three. That draft exceeded the compile limit: a redundant concrete identity comparison
had a kernel timeout, and the final concrete-to-generic conversion unfolded pullback
compactifications and chosen derived resolutions. The generic constructions repair the
cause within the item rather than raising the time limit or splitting the module.

The DAG's Noetherianity argument for the fibre product is unnecessary for the exchange
coherence API used here. Every theorem signature is preserved. There are no disputed
statements, target changes, new nodes or forced adaptations of another group's module.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
