# Nested experiments: NativePullTensor

Case: AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTotalTensor and its
adjacent Exists.choose declarations. Snapshot: Lean 4.35.0, master
revision 1ef1fddac73e, one Lean thread, synchronous elaboration.

## Baseline and preserved context

The existing module baseline is 268.39 CPU s, 272.53 wall s, and
7,926,140 KB peak RSS with Kernel checking. The four hot declarations are
51.5, 80.5, 79.3, and 52.5 s. The same stored terms are replayed by
probes/nd/ValuePrefixes.lean and MajorAlignment.lean; no source priority
change is used to rewrite an imported term.

The cost site is retained exactly: the two application-domain conversions
under the 12 original binders of @Exists.choose, and the source/target
endpoint conversions in the final Iso result. The consumer remains the
real Iso endpoint and nested Functor.obj/composition expression.

## Experiment A: representation symmetry

Representation producer A is the functor major premise stored on the
inferred side; B is the definitionally equal concrete premise stored on
the declared side. Both are real Functor.uncurry constructions in the
original Functor.obj consumer. The explicit replay checks the stored
terms, so instance synthesis is not mixed into the Kernel timings.

| Variant | Same conversion | Kernel result |
|---|---|---:|
| Original A/B, source endpoint | Functor.obj major-premise pair | 11,396 ms |
| A/A alignment, source endpoint | same pair after replacing only the right premise | 0 ms |
| Original B/A reverse control | same pair in reverse direction | 11,284 ms |
| regular/regular same-body control | same body under regular definitions | 0 ms |
| abbrev/abbrev same-body control | same body under abbrev definitions | 11,251 ms |
| regular/raw and abbrev/raw | same consumer, mixed vocabulary | 11,295/11,299 ms |

The aligned object type is structurally identical to the original right
object type and Kernel-checks. Thus the theorem obligation and endpoint
consumer are unchanged. The source compilation is the inference
measurement; MajorAlignment.lean is the explicit-instance Kernel replay.
This is a positive Level-1 result for representation asymmetry and the
Functor.obj projection path.

## Experiments B and C

The assigned Batch-1 extension was attempted only conditionally. A deeper
synthetic class chain or a repeated-field surrogate would remove the
dependent Exists.choose/Iso consumer and would violate section 2.1. No
valid depth or fanout control was therefore claimed. The existing four
declarations already show repeated endpoint/domain conversions, but that is
an observation, not a controlled C result.

## Experiment D: provenance audit

LEFT: the original declaration is local to the NativePullTensor module; its
data-bearing structure is an Iso whose endpoints are concrete Functor.comp
values. The functor major premise is produced by the stored concrete
construction and Functor.obj accessor. The endpoint contains named/let-bound
functor data and generated proof fields.

RIGHT: the declared type is imported from the same declaration and contains
the alternate concrete functor premise selected during the declaration's
construction. The right side is not rewritten by later local instances.
Both sides use the same outer Iso and endpoint vocabulary; the first
divergence is the Functor.obj major premise (and, in the full type diff, a
generated _proof_3 versus Sheaf.monoidalPreadditive).

The producer pattern is therefore concrete functor construction plus an
abbrev field accessor, not uncontrolled instance search. The ValuePrefixes
probe separately records the two dependent-domain conversions (23,012 and
23,065 ms); individual argument checks are at most 6 ms.

## Matched fast control and interpretation

The final nativePullTensor declaration in the same module has the same
functor/iso vocabulary but no large cross-representation conversion. Its
cheap self-comparisons are a context-preserving control. The aligned A/A
variant is also a direct fast control.

Outcome: A is confirmed at Level 1. The measured change is Kernel-side and
survives explicit replay. B/C are not established because a valid
context-preserving depth/fanout harness was unavailable; D identifies the
repeatable producer as an abbrev accessor over separately constructed
functor major premises.
