## What changed

In `Sheaf.Paper.IsomorphismFiniteExchangeCoherence`, filled the proofs of
`WeilConjectures.FiniteExchangeCoherence.canonicalAgreement`, `horizontal`, and
`coefficient`. Canonical agreement rewrites the supplied square and open comparison
to the ordinary representatives. Horizontal pasting specializes `ordinaryPasting`.
Coefficient compatibility expands the compact-support comparison, applies the
existing proper and open coefficient clauses, and combines these with naturality
of the lower-level proper exchange using `mapped_combine`.

Added a proof-only `import all Sheaf.Paper.RelativeCompactSupportPasting` to access
its normalization and composition helpers. Suppressed unused-section-variable
warnings caused by preserving the existing theorem signatures, and the unused
`hK` warning locally for `coefficient`: its factorwise argument proves the square
on all inputs, hence in particular on the specified finite-Tor domain.
Removed three unused proof imports listed below. No definitions, signatures, public
imports, or other modules changed.

## Proved and sorry left

Closed 3 of the item's original 8 holes, with no added holes:

- `WeilConjectures.FiniteExchangeCoherence.canonicalAgreement`.
- `WeilConjectures.FiniteExchangeCoherence.horizontal`.
- `WeilConjectures.FiniteExchangeCoherence.coefficient` (from the already stated
  proper and open coefficient clauses, which remain open).

The following 5 original named theorem holes remain, all attached to
`lem-pur-isomorphism-finite-exchange-coherence`:

- `WeilConjectures.FiniteExchangeCoherence.identity`.
- `WeilConjectures.FiniteExchangeCoherence.vertical`.
- `WeilConjectures.FiniteExchangeCoherence.compositionIsIso`.
- `WeilConjectures.FiniteExchangeCoherence.properCoefficient`.
- `WeilConjectures.FiniteExchangeCoherence.openCoefficient`.

The completed proofs compile through `lcompile.py`. No new statements or
split-off holes were introduced.

## No longer needed

Removed unused proof imports:

- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.
- `Sheaf.CategoryTheory.Adjunction.CoefficientExchange`.
- `Sheaf.SixFunctors.OpenTensorNormalization`.

No node or module is withdrawn: these three remain planned dependencies of the
unfinished factor clauses. The completed horizontal and coefficient arguments
follow the existing node's steps 2 and 6. The unit route and node dependency plan
for the five remaining holes are preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or incompatible dependency was found. The existing node's
horizontal specialization and factorwise coefficient assembly are directly
usable. The identity clause still needs a derived-category transport of the
module-level identity normalization; an attempted direct use of module-level
maps was discarded rather than changing its statement.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
