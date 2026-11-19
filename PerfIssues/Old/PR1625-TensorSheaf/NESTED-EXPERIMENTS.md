# Nested experiments: PR #1625

Case: AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison_app_app_fac.
Snapshot: Lean 4.35.0, master revision 1ef1fddac73e, one thread,
synchronous elaboration, maxHeartbeats 10000000.

## Baseline and preserved context

The before prefix is 188.18 CPU s, 189.31 wall s, and 8,245,292 KB peak
RSS; the after prefix is 104.15 CPU s, 104.95 wall s, and 2,929,672 KB.
The target Kernel check is 87.6 s before and 2.43 s after. The exact site
is the final inferred/declared type conversion: an Eq whose left side is a
CategoryStruct.comp containing nested NatTrans.app applications. The
28-argument source application itself checks in 335 ms.

## Experiment A: representation symmetry

Path A is the concrete natural-transformation major premise in the inferred
left NatTrans.app; path B is the definitionally equal concrete premise in
the declared right expression. Both are retained under the original Eq,
CategoryStruct.comp, NatTrans.app, and dependent result type. The explicit
replay is probes/nd/G3B-NatTransMajor.lean.

| Variant | Same final conversion | Kernel result |
|---|---|---:|
| Original A/B | outer NatTrans.app major-premise pair | 95,869 ms |
| A/A alignment | replace only right major premise | 0 ms |
| Reverse B/A | original right versus aligned right | 93,567 ms |
| Fixed theorem control | same statement via whole-NatTrans equality | target 2.43 s |

The aligned term has a structurally identical checked result type. Thus the
dependent theorem obligation is preserved. Source compilation supplies the
implicit inference measurement; the probe uses explicit stored terms for
Kernel replay. This confirms a Level-1 mixed-representation conversion.

## Experiment B: nesting amplification attempt

The same mismatch occurs at two retained NatTrans.app levels. The inner
argument-6 pair under the outer CategoryStruct.comp takes 95,717 ms; the
enclosing left-composition argument takes 96,236 ms. These measurements
show that the nested consumer preserves the cost, but they are not a
factorial depth ladder: adding a synthetic class layer would change the
dependent NatTrans type and the cost site. We therefore mark B
inconclusive rather than treating the two existing nodes as controlled B0/B1
variants. No instance-synthesis time is assigned to the Kernel numbers.

## Experiment C

No repeated-field fanout control is valid for this declaration. The slow
pair is one accessor major premise in a dependent Eq result; duplicating it
in a synthetic class would no longer be the same consumer. The source
statement has nested occurrences, but no unused or independently declared
field is counted as repeated work.

## Experiment D: provenance audit

LEFT: the old proof constructs a concrete component of the derived tensor
comparison. Its data-bearing structure is a natural transformation consumed
through CategoryStruct.comp and NatTrans.app. The major premise is obtained
through the concrete derived-functor/instance route.

RIGHT: the expected type stores the corresponding concrete transformation
from the instantiated theorem. It was elaborated earlier and is not changed
by local priorities. The first timed divergence is the NatTrans.app major
premise at argument 6; the carrier, category, and other arguments are
0--2 ms. The after proof first establishes equality of whole natural
transformations, so the component conversion is not reconstructed.

## Matched fast control and interpretation

The earlier declaration in the same module costs about 15.4 s in both
prefixes and has the same derived-category context, serving as a nearby
control. The after proof is a stronger statement-level control but changes
the construction route and is not used as sole causal evidence.

Outcome: A is confirmed at Level 1. B is an explicitly recorded negative
attempt: the natural nesting retains the cost, but no valid independent
depth parameter can be introduced without changing the obligation. C is not
established. D identifies the concrete NatTrans major-premise construction
under an abbrev projection as the repeatable producer.
