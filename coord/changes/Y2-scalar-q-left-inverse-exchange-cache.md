# Cache the scalar exchange through its existing fixed-endpoint wrapper

Item: `Sheaf.Paper.RationalP1ScalarChernQLeftInverse` (Y2).

The proof descends the existing P2 splitting through proper base change. To use
that exchange, its `IsIso` proof must match `secondTraceExchange`. Expanding the
old inline native-functor construction caused a kernel timeout: a diagnostic
with a lowered 100000-heartbeat budget spent about 50--58 seconds in kernel type
checking and took more than 60 seconds overall. The line-membership and native
exchange proof alone compiled in 6.9 seconds. Private generic copies and their
comparison also encountered the expanded-functor kernel timeout.

Changed existing module: `Sheaf.Paper.RationalP1SecondPretraceData` (unclaimed in
the shared claim records). Its existing `secondPretraceExchangeMap` already
constructs exactly the native exchange with the fixed module-object endpoints,
and `secondPretraceExchangeMap_isIso` already transfers native invertibility.
The body of `secondTraceExchange` now composes that existing wrapper with the
same pushed-forward `firstLineComparisonForTrace.hom`. Its definition is moved
below the wrapper API to make that reference available. Its signature,
visibility, attributes, public imports, and mathematical composite are unchanged.
No existing declaration is added, removed, or renamed in this module. Its node
records the cached composition. No source-library file is changed.

The three direct importers are `Sheaf.Paper.RationalP1SecondPretrace`,
`Sheaf.Paper.RationalP1SecondExchangeProjection`, and
`Sheaf.Paper.RationalP1SecondProjectionInterchange`. They are checked against the
changed file without retaining unchanged source copies in the delivery.

Validation completed: `lcompile.py --all` compiled the changed data module in
2.5 seconds, the completed item in 27.3 seconds, and the three direct importers
unchanged in 31.4, 11.3, and 14.0 seconds respectively. Their temporary source
copies were removed after this check. There are no forced consumer adaptations.
Both edited Lean modules contain zero `sorry` tokens, and the item theorem's
signature is byte-identical to the original.
