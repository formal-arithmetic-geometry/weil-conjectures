## What changed

Proved `WeilConjectures.PurityFiniteSetting.finiteReductionOrientationExceptionalComparison_isIso`
without changing its signature or any existing proof. The existing ordinary orientation
definition is factored through a definitionally identical generic supported adjunct. Added the private proof
import `Sheaf.Paper.FiniteReductionExceptionalFiniteModel`.

At positive levels n+1 and m+1, apply the existing finite exceptional model to the zero
section and the shifted root-line input. The input is finite-Tor constructible by
`finiteReductionLineInput_constructible`. The model's counit normalization satisfies the
specification of `existsUnique_finiteReductionOrientationExceptionalComparison`; uniqueness
identifies its isomorphism hom with the specified comparison. `Iso.isIso_hom` finishes.
The impossible zero levels are discharged using the existing positivity hypotheses.

Updated the existing orientation node's proof and proof dependencies to record this route.
The unit route is unchanged. Equal positive levels and empty schemes require no special
hypothesis; the model and its counit identity already cover them. No quotient flatness or
ramification divisibility is assumed.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.PurityFiniteSetting.finiteReductionOrientationExceptionalComparison_isIso`
(node `def-pur-finite-affine-orientation-comparison`).

No sorry remains in the item. Added zero holes and zero split-off statements. The proof
uses the existing `finiteReductionExceptionalFiniteModel_counit` theorem (node
`lem-pur-finite-reduction-exceptional-model-counit`), whose proof is still sorry in its own
module; that pre-existing dependency was not changed by this delivery.

## No longer needed

None. All previous imports and dependency nodes still serve the existing constructions
and proofs. The remaining invertibility assertion needs no separate closed-purity or
rank-one balancing lemma: the existing general finite exceptional model applies directly.
No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The node left this isomorphism assertion as an open obligation and the theorem's original
proof sketch suggested a separate closed-purity computation. The already stated general
finite exceptional model and its counit normalization give the shorter route above.

Searches run through msearch: LeanFinder for exceptional inverse image and finite coefficient
reduction returned derived-functor and flat-model infrastructure, with no exact comparison;
Loogle for `CategoryTheory.IsIso, CategoryTheory.Iso.hom` found `Iso.isIso_hom`; Mathlib grep
for exceptional quotient/isomorphism and finiteReductionExceptional returned no hits.
The initial compile had no Lean errors but exceeded the file limit at 73.8 seconds.
A profiling compile passed at 47.0 seconds. A later nonprofiling run took 88.6 seconds;
detailed tracing located 33.5 seconds in the existing finiteReductionEtaleOrientation
kernel check and 9.65 seconds in its generated _proof_15. Applied the existing local
cached derived-category instance pattern to that definition alone. Because a subsequent
compile still took 72.7 seconds, factored its unchanged mathematical construction into
`finiteReductionSupportedOrientationAdjunct`, which keeps the ring and immersion as
parameters and the HasExt instance as a proof parameter. The original map specializes this explicit construction and is definitionally
equal to its old body; the helper is recorded on the existing definition node.
Profiler options were removed. The finite-Tor input in the new proof is explicitly typed.
Change record: coord/changes/F9-affine-etale-orientation-instance-context.md.
All 49 downstream consumers retain definitionally identical interfaces and need no adaptation.
The new helper is a real data construction with no sorry and makes no arbitrary choice.

Project rg found the model and its counit theorem in
`Sheaf.Paper.FiniteReductionExceptionalFiniteModel`, and the analogous smooth-case proof in
`Sheaf.Paper.FiniteReductionComparisons`. No new statement or definition was needed.

The factored version compiled in 63.5 seconds; a focused profiling run then passed in
51.6 seconds. All tracing and print commands are removed for the delivery compile.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
