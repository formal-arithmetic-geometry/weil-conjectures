# ImageHomCounit workplan experiments

Source snapshot: `imageHomIso_counit`, module
`AlgebraicGeometry/IndEtaleMapping/IndEtaleDerivedImageHomCounit`,
commit `212f97dd22a`; Lean and Mathlib 4.35.0. The cost site is
the final inferred-type/declared-type conversion at `exact h`,
where `h` is the unchanged `conjugateEquiv_counit` application.
`probes/HeadAudit.lean` retains the original context and pair:
both sides are `Eq` propositions over `CategoryStruct.comp`;
the first difference in the morphism type is inferred raw
`DerivedCategory (Sheaf ...)` versus declared
`DerivedCategoryModule A X`. The distinction also occurs in
both equality sides. The wrapper is an abbrev whose immediate body
exposes the raw derived category.

All timings use one Lean thread, `timeout 3600`,
`/usr/bin/time -v`, normal Kernel checking, and the same
200,000-heartbeat limit. Kernel-only time and heartbeat consumption
are not separately available. The baseline in this workplan session,
`probes/FinalExact.lean`, succeeds in 54.94 s wall,
53.90 + 1.08 s CPU, 7,487,640 KB RSS. The helper application alone
was 2.70 s in the head audit; the final conversion carries the cost.

## C2-W: Unfold only the declared wrapper

EXPERIMENT: C2-W; group: G3-A. Hypothesis: the raw/wrapper head
difference alone explains the long final conversion. BASELINE:
the exact pair and 54.94 s final check above. CONTROL:
`probes/wp/UnfoldWrapper.lean` applies a Lean term elaborator
to the original declared equality. It performs one delta step
on each original `DerivedCategoryModule` occurrence, without
changing the equality's other terms or the `conjugateEquiv_counit`
proof construction. The generated target is definitionally equal
to the original theorem obligation. Normal Kernel checking remains
enabled. `UnfoldWrapperHead.lean` confirms that the first
raw/wrapper child is now a raw `DerivedCategory` on both sides,
so the elaborated pair really changed. Its first syntactic
difference is a `HasSheafify` proof argument. A structural
traversal that skips arguments of proposition type finds the next
data mismatch at `nonproof.1.3.5.3`: a nested
`DerivedCategoryModule` versus raw `DerivedCategory`.

RESULT: the same final conversion succeeds but costs 83.45 s
wall, 82.29 + 1.18 s CPU, 9,865,804 KB RSS. The wrapper-only
control does not remove the cost and is slower than baseline.
Supports: the first wrapper exposure is insufficient; at least
one nested representation difference remains. Weakens: the
outer wrapper/raw mismatch is the complete cause. The diagnostic
head probe takes 2.30 s wall, 1.68 + 0.72 s CPU,
3,042,760 KB RSS and ends in `sorry` after printing the pair;
it is not counted as a proof. Classification: necessary first
unfolding followed by an unfavorable nested path. Confidence:
confirmed negative result for wrapper-only alignment; the
individual nested leaf's share of the 83 seconds is unresolved.

## C2-I: Fully aligned inferred target

EXPERIMENT: C2-I; group: G3-A. Hypothesis: the expensive final
conversion disappears when the declared equality uses the
existing proof term's exact inferred representation. BASELINE:
the same `exact h` proof and 54.94 s check above. CONTROL:
`probes/wp/UniformInferred.lean` declares the goal with
`type_of%` applied to the exact original `conjugateEquiv_counit`
term, then uses the same `have h` and `exact h` proof. This
changes the entire goal representation, so it is a full-alignment
control rather than a one-leaf test; the proposition remains
definitionally equal to the original obligation. Normal Kernel
checking is enabled. `UniformInferredHead.lean` verifies that
the type argument and both equality sides are syntactically
equal in the actual and expected elaborated pair.
RESULT: success in 2.60 s wall, 1.73 + 0.90 s CPU,
2,816,600 KB RSS. The final conversion is immediate at the
pair level. The diagnostic head probe takes 2.00 s wall,
1.38 + 0.70 s CPU, 3,029,788 KB RSS.
Supports: representation alignment, with the original proof
term unchanged, removes the cost. Weakens: the original proof
body itself is intrinsically expensive. Unresolved: which
particular nested endpoint or instance mismatch dominates.
Classification: unfavorable representation path avoided by
full alignment. Confidence: confirmed for the aligned control.

## Negative source controls

The earlier `UniformRaw.lean` and `RegularWrapper.lean`
source-spelling variants both leave the elaborated pair unchanged
and remain near 55 seconds. They are not interpreted as
counterexamples to C2-W or C2-I. Their head probes are retained
outside `wp` with the original head audit.

## Mechanism

The original proof's type and target have the same equality and
composition heads, but their derived-category arguments store
different wrapper representations. Exposing the first wrapper
does not resolve a further nested wrapper/raw difference and
does not make the check cheap. A goal expressed in the exact
inferred representation checks quickly with the original proof.
The evidence establishes a multilevel representation mismatch,
without attributing the long Kernel path to a specific internal
unfold or to the differing proof arguments.
