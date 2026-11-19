# Nested experiments: PR #1556

Case: AlgebraicGeometry.ProEtale.not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety.
Snapshot: Lean 4.35.0, master revision 1ef1fddac73e, one thread,
synchronous elaboration. Existing before/after records are reused.

## Baseline and context

The historical prefix is 59.47 CPU s, 60.57 wall s, and 7,760,464 KB
peak RSS; the fixed prefix is 4.75 CPU s, 5.73 wall s, and 3,056,716 KB.
The target's in-situ Kernel check is 54.9 s before and below the profiler
threshold after. The retained consumer is the original nested Exists.intro
and generated congr proof proposition. No local instance priority is used.

## Experiment A: representation symmetry

The first divergent data-bearing object is the concrete Iso/NatTrans major
premise in the left CategoryStruct.comp of the generated congr proposition.
Path A is the original whiskered Iso term; path B is the definitionally
equal term already present on the other side. The control in
probes/nd/G3B-ClosingNatMajor.lean replaces only that major premise and
checks the resulting term at the original dependent proposition.

| Variant | Same proposition conversion | Kernel result |
|---|---|---:|
| Original A/B | congr proof proposition domain | 50,090 ms |
| A/A major-premise alignment | same domain and outer congr consumer | 0 ms |
| Reverse B/A | same conversion, opposite direction | 50,585 ms |
| Existing fixed closing proof | same theorem statement, cancellation proof | target check below 50 ms |

The aligned proposition type is structurally unchanged and the term
Kernel-checks. The source compilation is the inference measurement; the
probe explicitly replays the stored major-premise terms. The enclosing
Exists.intro, id, and Eq.mp domains each compare immediately, so this is a
context-preserving Level-1 result rather than a tactic timing claim.

## Experiments B and C

Batch 1 assigns only the provider-path control when the original context is
retained. A depth ladder or repeated-field class would change the generated
congr proposition and is not a valid control here. We therefore record no
unsupported B/C trend. The proposition does contain nested accessor use,
but that is observational evidence only.

## Experiment D: provenance audit

LEFT: the old local declaration closes the branch with a concrete
whiskered shift-isomorphism component. Its data-bearing structure is an Iso
and its NatTrans.app component, built through the derived-functor instance
route and then consumed by CategoryStruct.comp.

RIGHT: the expected proposition carries the corresponding term from the
instantiated congr theorem. It was elaborated before this probe and is not
rewritten by local priorities. The first timed divergence is the NatTrans
major premise under the left composition; the outer Eq and carrier are
cheap. The fixed form instead transports h.trans zero_comp.symm through
cancel_mono, avoiding the concrete component comparison.

The producer pattern is a concrete wrapper/component assembled in the old
closing proof, not a demonstrated instance-synthesis slowdown. The
ClosingCongrDomain probe records the exact instantiated proposition and the
same 50-second conversion.

## Matched fast control and interpretation

The preceding theorem in the same source context costs about 2.03 s in the
old file and is a matched fast control for the surrounding imports and
dependent categories. The fixed closing proof is a second control, but its
proof construction is intentionally treated as an API control rather than
proof of a single source rewrite.

Outcome: A is confirmed at Level 1 for the generated dependent proposition.
The expensive work is Kernel-side and disappears under a type-preserving
major-premise alignment. B/C are not claimed; D identifies the old concrete
whiskered Iso/NatTrans construction as the representation producer.
