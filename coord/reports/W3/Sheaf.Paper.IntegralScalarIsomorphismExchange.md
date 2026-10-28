## What changed

Proved `WeilConjectures.IntegralScalarExchange.integralScalarIsomorphismExchange_integral`
in `Sheaf.Paper.IntegralScalarIsomorphismExchange`. The existing strict-limit theorem already
identifies both integral paths after the same three invertible target maps. Evaluating its
last clause twice and cancelling their composite gives the required equality.

Moved this theorem after `strictLimitEquation_of_integralScalarIsomorphismExchange`, keeping
its signature and docstring unchanged. Added the proved private helper `positive_ramification`:
the image of the source uniformizer is nonzero and nonunit, hence is a unit times a positive
power of the target uniformizer. Equality of its principal ideal is the required ramification
hypothesis. This argument follows the existing private `RamifiedPullback.ramification_exists`
proof, without importing its geometric comparison machinery. No imports changed.

Updated the parent DAG proof to record the cancellation argument and its DVR dependency.

Validation: the final module compiled cleanly on the project server in 29.5 seconds,
with no warnings. The delivery tool runs the required declaration/axiom probe.

## Proved and sorry left

Closed 1 of the 7 holes present in the copied item:
`WeilConjectures.IntegralScalarExchange.integralScalarIsomorphismExchange_integral`.
Added 0 holes and split off 0 statements. This proof uses the existing, still unproved
strict-limit clause; it does not claim the whole scalar-exchange theorem is axiom-free.

The six remaining holes are:

- `WeilConjectures.IntegralScalarExchange.openInverse_isIso`
  (node `lem-pur-integral-scalar-isomorphism-exchange`).
- `WeilConjectures.IntegralScalarExchange.finiteScalarIsomorphismExchange`
  (node `lem-pur-integral-scalar-isomorphism-exchange-finite-level`).
- `WeilConjectures.IntegralScalarExchange.strictLimitEquation_of_integralScalarIsomorphismExchange`
  (node `lem-pur-integral-scalar-isomorphism-exchange-strict-limit`).
- `WeilConjectures.IntegralScalarExchange.scalarPull_finiteTor`
  (node `lem-pur-integral-scalar-isomorphism-exchange`).
- `WeilConjectures.IntegralScalarExchange.rectangle_refinement`
  (node `lem-pur-integral-scalar-isomorphism-exchange`).
- `WeilConjectures.IntegralScalarExchange.Systems.strictScalarIsomorphismExchange`
  (node `lem-pur-integral-scalar-isomorphism-exchange`).

The previously proved `finiteCoherent`, `rectangle_naturality`, and main conjunction assembly
are retained.

## No longer needed

None. No imports or modules are pruned: the original system, finite-coefficient, and
normalization dependencies remain necessary for the six unfinished clauses. The integral
clause itself no longer needs an independent proof of coefficient exchange; it uses the
already stated stronger normalization clause.

## Where the brief, the DAG or earlier work was wrong

The copied module already had the V4 conjunction decomposition, with seven holes, rather
than a hole in the main conjunction. The stale build-error file reports failed dependency
imports; the initial server compile of the copied current module succeeded in 32.5 seconds.
There is no queue rework row or return for this item in the shared snapshot.

The final strict-limit equation contains enough information to deduce the integral equality.
This avoids duplicating that argument and introduces no circular theorem dependency: the
strict-limit theorem and its node do not depend on the integral equality theorem.

Searches: LeanFinder for scalar adjunction/mate naturality returned general adjunction and
tensor lemmas; Loogle for `CategoryTheory.mateEquiv, CategoryTheory.NatTrans.naturality`
returned no hits. Local searches located the existing strict-limit clause and the private
DVR argument in `RamifiedPullbackTowerIdentification`; cancellation and ideal mapping are
provided by Mathlib. No new mathematical statement was needed. The proof covers identity
extensions and ramified extensions alike; positivity excludes exponent zero because the
source uniformizer remains nonunit in the target.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralScalarIsomorphismExchange": "37c2b9541d522fbde90ad7b000d9434b15947548"}, "results": {"Sheaf.Paper.ZlFrameworkOpenExchange": {"hash": "817d737b9ee39d4db3caf4e5d27ae2865eee2c92", "status": "OK"}}, "seconds": 72, "time": "2026-10-28T07:49:34+0800", "transitive": 0, "version": 1}
```

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
