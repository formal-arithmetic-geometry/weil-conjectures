## What changed

Proved `frobeniusSystemDirect_isIso` and `frobeniusSystemCompact_isIso` in
`Sheaf.Paper.FrobeniusSystemExchangeInverse` without changing their signatures.
The canonical system pullback composition and unit comparisons construct a quasi-inverse
for pullback along any scheme isomorphism. The existing proved mate-isomorphism theorem
then makes the actual direct system exchange invertible. Apply the same argument to
the proper part of the retained compactification and compose with the existing open
system isomorphism for the compact case. All inputs remain arbitrary unbounded systems.

Added two proved private helpers and the private proof import
`Sheaf.CategoryTheory.MateIsoAlongEquivalences`. Updated the two theorem docstring proofs
and the DAG to record this shorter route. All public imports, definitions and declaration
signatures stay as before. No consumers or source-library modules are changed.

## Proved and sorry left

Closed 2 of 8 original holes:

- `WeilConjectures.FrobeniusExchange.frobeniusSystemDirect_isIso`
- `WeilConjectures.FrobeniusExchange.frobeniusSystemCompact_isIso`

Added zero holes and zero nodes. Six original holes remain, attached to
`lem-weil-frobenius-system-exchange-inverse`, with their original source and proof docstrings:

- `WeilConjectures.FrobeniusExchange.frobeniusSystemDirect_inverse_evaluation`
- `WeilConjectures.FrobeniusExchange.frobeniusSystemCompact_inverse_evaluation`
- `WeilConjectures.FrobeniusExchange.frobeniusDirectIntegral_isIso`
- `WeilConjectures.FrobeniusExchange.frobeniusCompactIntegral_isIso`
- `WeilConjectures.FrobeniusExchange.frobeniusDirectIntegral_inverse`
- `WeilConjectures.FrobeniusExchange.frobeniusCompactIntegral_inverse`

The two closed theorem proofs use the canonical system compositor/unit interface and
the proved generic mate theorem. Existing dependencies can still rest on sorry;
this report claims closure only of these two theorem bodies.

## No longer needed

Removed unused private import `Sheaf.Paper.CompletedRlimFunctor`. The item already has
its actual limit functor through the public operation-realization interface.

For the two proved invertibility declarations, neither the finite exchange inverse lemma
nor joint conservativity of evaluation is needed. Pullback equivalences prove the actual
system mate invertible directly. The remaining six holes retain their original proof
plan and dependencies, so this delivery does not globally prune those nodes or modules.
No module or node is withdrawn, and no top-level tool approval is removed.

## Where the brief, the DAG or earlier work was wrong

The DAG's proposed evaluation-plus-joint-conservativity route is unnecessary for the
first two invertibility assertions. Canonical system composition and identity comparisons
already give a quasi-inverse to scheme-isomorphism pullback. The unit route is preserved;
this node is not itself a binding realization of the unit's statement or steps.

Attempted evaluation and integral inverse proofs are not included in this packet.
The concrete evaluation coordinate simplification unfolded large chosen pullback and
limit constructions and exceeded the single-file time limit. That exploratory proof
was removed; the two short system proofs use existing composition and unit interfaces
without unfolding their constructions. No limit increase or proof-file split is used.

One compile failed before Lean started because the server temporary filesystem lacked
space; later requests ran. The final packet is checked by the required delivery tools.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
