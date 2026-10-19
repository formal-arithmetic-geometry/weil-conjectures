# LocalFrobeniusTrace transparency option

## Reason
The completed proof avoids expensive unfolding in dependent coefficient constructions by retaining the module-level transparency setting used by the delivered file. Preflight correctly classifies this as an interface-visible command change and requires a stage-3 record.

## Old
set_option backward.isDefEq.respectTransparency false

## New
set_option backward.isDefEq.respectTransparency true

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.LocalFrobeniusTrace | R6 | The module's elaboration uses the transparency setting; declaration signatures are unchanged. |

## Status
landed 20261019T231329-L-574840 2026-10-19 (merge of deliver/R6/Sheaf.Paper.LocalFrobeniusTrace)
