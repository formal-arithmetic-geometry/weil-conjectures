## What changed

Added the restricted comparison module `Sheaf.Paper.NativeProperScalarMateBoundedBelowRestricted` and imported it from the assigned module. The assigned theorem now obtains the restricted isomorphism and reflects it through the exact conservative derived restriction functor. The parent DAG proof and dependency list were updated to record this route.

## Proved and sorry left

Closed `native_proper_scalar_mate_bounded_below`. The strictly simpler restricted component theorem `native_proper_scalar_mate_bounded_below_restricted` remains as one named sorry, with node `lem-sf-native-proper-scalar-mate-bounded-below-restricted`.

## No longer needed

The original multi-stage proof dependencies for coefficient factorization and mate pasting are not imported by the delivered module itself; the proof uses the restricted comparison node and the existing restriction-reflection API. Those lower nodes remain in the DAG because they are still reachable elsewhere. No additional imports were removed from the source snapshot.

## Where the brief, the DAG or earlier work was wrong

The assigned module had only a sorry while its existing proof route was already represented by a restricted comparison split in the archived delivery. Restoring that split and recording the reflection argument makes the parent proof compile against the current source snapshot. The restricted analytic comparison remains a genuine lower-level obligation rather than being asserted through an instance.

## New nodes

`lem-sf-native-proper-scalar-mate-bounded-below-restricted` records the restricted proper scalar-mate component used by the parent. Its statement is strictly simpler because it asks only for invertibility after exact derived restriction along the target coefficient map.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeProperScalarMateBoundedBelow": "0714c8682710fb32488a8bbda3cf9d0980e7e183", "Sheaf.Paper.NativeProperScalarMateBoundedBelowRestricted": "9bdd84890277d607f787e5b3a5664d79ed754e6e"}, "results": {"Sheaf.Paper.NativeCompactSupportScalarMateInvertible": {"hash": "ab58f1701c4fb3b02c1aceef1ce25df67ed058ee", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T06:45:40+0800", "transitive": 0, "version": 1}
```

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
