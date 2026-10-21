# AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_exchange_source_adjunct

## Reason

The assigned row in coord/rework.tsv preserves this module in quarantine after a cluster
restoration was reverted. Its live source is absent, but the exchange equality parent still
needs both its theorem and its DAG attachment. Restore the existing complete proof at its
original module path. The archived proof initially failed with an unknown constant
`AlgebraicGeometry.ProEtale.CondensedRing.derivedPushSource` during the simplification in
`integral_push_counit`. An explicit proof import of the post-sync ChangeOfCoefficients
companion supplies this named functor. No dependency implementation is changed.

## Old

The live path `lean/Sheaf/Paper/ContinuousIntegralExchangeSourceAdjunct.lean` is absent.
The authoritative source is
`quarantine/Sheaf/Paper/ContinuousIntegralExchangeSourceAdjunct.lean`.
Its public declaration is
`AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_exchange_source_adjunct`.
It also contains the proved private lemmas `coefficient_counit`, `source_normal_form`,
`baseChange_adjunct`, `bounded_counit_hom` and `integral_push_counit`.

## New

Restore that entire archived module, preserving all declaration signatures, proof bodies,
docstrings, attributes, universes, geometric and coefficient hypotheses and public imports.
The only differences from the archive are whitespace wrapping to at most 100 columns and
this proof-only import:

```lean
import Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
```

The proof first calculates a generic adjunct normal form using naturality, then identifies
the coefficient push/counit composite by Mathlib's iterated mate/conjugation and inverse mate
counit identities. Fully faithful restriction gives the bounded constructible counit formula.
The final theorem specializes these calculations. All these proof steps remain complete.
There is no definition or statement change, no new choice, no new hole and no change to a
target's meaning. The node, its Lean attachment and all its dependencies remain unchanged.

## Users

`tools/downstream.py Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct --allow-missing
--names` reports no live consumer. A separate scan of both live roots and both quarantine
roots finds the archived direct consumer below. It is also the DAG parent via
`lem-weil-pbc-continuous-integral-exchange-equality`. Its original import and application
remain valid with the identical signature; no adaptation or parent withdrawal is needed.
No local claim record exists for that consumer when this packet is prepared.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Archived direct consumer; theorem and its complete interface restored unchanged. |

## Status

landed 20261021T021026-L-2693447 2026-10-21 (merge of deliver/T2/Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct)
