# Workplan report

Lean 4.35.0, master revision `1ef1fddac73e`, one Lean thread. Measurements
are ordinary Kernel checks; typed-sorry or failed controls are diagnostic
only. The source theorem obligations were not changed.

| Case | Experiments | Outcome | Mechanism statement | Confidence |
|---|---|---|---|---|
| #1624 | G1-A/B/C | Same `Functor.comp` heads; args 2/3/6/7 are locally unequal, while whole endpoints cost 14.740/28.323 s; all isolated alignments are ill-typed; one-step body is `Functor.mk` | Concrete dependent composition arguments defeat cheap same-head congruence; reduction is required | Strongly supported |
| #1563 | G1-A/B | Outer right `CategoryStruct.comp` costs 31.026 s; nested arg 6 costs 21.537 s; one-factor controls remain 11.325--20.810 s | Nested concrete composition/accessor path dominates the dependent `Eq` domain; nested arg 5 is a contributor, not the sole trigger | Strongly supported |
| #1627 | G2-A/B/C, G4-A | Generated `_proof_1/_proof_2` value checks cost 20.228/33.699 s; final conversions 0 ms | Generated proof value reaches an expensive instantiated `id` proposition domain | Plausible |
| #2122 | G4-B | 379.92 s CPU, 16,327,872 KB RSS; motive/witness branches check in 16.115/18.419 s; final dependent branch cannot be isolated | Branch-boundary work is confirmed, but no exact inner conversion or recursor-causality claim is established | Unclassified |
| #1625 | D3 positive control | `NatTrans` major-premise alignment: 95.869 s to 0 ms | Accessor major-premise mismatch drives final type conversion | Confirmed |
| #1556 | B4/D4 positive control | `NatTrans` major-premise alignment: 49.548 s to 0 ms | Same accessor mismatch inside generated proof proposition | Confirmed |

## Cross-case observations

The same-head cases (#1624 and #1563) show that local argument checks can be
cheap while the enclosing conversion is expensive. The positive controls
show the complementary case: a single concrete accessor major premise can
account for almost all of a final type or proof-proposition conversion.
Generated fields (#1627) and existential branches (#2122) locate where the
cost is stored, but do not by themselves identify a new mechanism.

## Interpretations and limits

The data support three recurring representation effects: concrete arguments
prevent cheap congruence, dependent instantiated propositions expose those
arguments at application boundaries, and accessor projections become
expensive when their major premises are not aligned. The exact internal
Kernel reduction sequence is not observable with the permitted ordinary
probes. #1563 and #1627 still need a decisive nested one-factor control, and
#2122 still needs an exact branch-local conversion pair.
