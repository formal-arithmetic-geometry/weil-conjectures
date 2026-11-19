# Workplan cross-case matrix

| Case | First mismatch | Conversion context | Successful control | Mechanism supported | Remaining uncertainty |
|---|---|---|---|---|---|
| #1624 | `Functor.comp` endpoint args 2/3/6/7 | final `Iso.trans` domain | endpoint argument table; all isolated alignments rejected as ill-typed | enclosing-definition-mediated same-head DefEq | dependent multi-argument alignment and exact body layer below `Functor.mk` |
| #1563 | nested `CategoryStruct.comp` arg 6 | `Eq.mpr` proof domain | type-preserving nested controls; arg 5 lowers 21.537 to 11.325 s but does not finish | same-head nested argument mismatch | projection versus remaining nested data work |
| #1627 | instantiated `id` proof proposition | generated law field | generated-prefix reconstruction | dependent proof-domain conversion | first nested proposition term |
| #2122 | motive/witness branches under `Exists.casesOn` | stored theorem value | binder-instantiated branch checks (16.115/18.419 s) | branch-boundary cost only; recursor not blamed | exact final dependent branch pair |
| #1625 | `NatTrans.app` concrete major premise | final result type | type-preserving major-premise alignment | accessor-induced final type conversion | inner nested major premise |
| #1556 | `NatTrans.app` concrete major premise | generated `congr` proposition | type-preserving major-premise alignment | accessor-induced dependent proposition | remaining proof detail |

The matrix records only measured or explicitly bounded outcomes. A source
spelling change without an elaborated-expression change is not counted.
