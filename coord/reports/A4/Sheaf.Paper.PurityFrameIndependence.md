## What changed

Replaced the `frameClass_independent` hole by a compiling proof: obtain a local finite
chain of elementary generator moves, induct on it using heterogeneous equality, and
apply the local equality criterion. Its signature and `frameClassOnPullback` definition
are unchanged. All added proof imports are non-public.

Added `FrameLocalGeneratorChains.lean`, with a complete proof of
`exists_frame_local_generator_chain` from the existing local generating-tuple theorem.
The proof identifies ideals on an affine chart, passes to the local stalk ring, spreads
each elementary operation, shrinks to identify intermediate and endpoint sections, and
restricts to an affine neighbourhood. Its private helpers are all proved.

Added `FrameElementaryMoves.lean` and `FrameClassLocalEquality.lean`, stating two separate
cohomological parts of the source argument. Each remaining theorem has exactly one
named `sorry`, a source, complete proof in words, and a new node. These results retain
the source's unit/scaling/swap/shear and bottom-degree descent route.

Local irreducibility attributes for `frameBoundaryProduct` and `frameClass` prevent
unnecessary unfolding during elaboration; they change no global attribute or definition.
The complete four-module compile passed (33.8, 2.2, 14.5, and 54.7 seconds); a separate
parent compile passed in 43.9 seconds. The local chain theorem alone passed in 34.6
seconds. No definitions contain holes.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.PurityFiniteSetting.frameClass_independent`.
Also proved the new theorem
`WeilConjectures.PurityFiniteSetting.exists_frame_local_generator_chain` and all its
private helpers.

Two holes added, both remaining:

- `WeilConjectures.PurityFiniteSetting.frameBoundaryProduct_elementary`
  (`lem-pur-frame-elementary-moves`): one elementary operation, without any local-chain
  or descent conclusion.
- `WeilConjectures.PurityFiniteSetting.frameClass_eq_of_locally_heq`
  (`lem-pur-frame-class-local-equality`): local equality implies global equality,
  with local equality explicitly assumed and no generator invariance asserted.

The item itself has zero remaining holes. This is a decomposition, with one original
hole closed and two strictly separate holes added, not a claim of a complete
axiom-free cohomological proof. Existing imported theorem holes are unchanged.

Edge cases checked against the statements: c=0 admits no elementary edge and its
local chain is reflexive; c=1 admits only unit moves; an empty scheme has no points
to check; unit ideals and zero ideals are permitted. Shears require distinct indices,
and are inverted by the negative coefficient. No regular-sequence or finite-type
hypothesis is silently added to the elementary-product result.

## No longer needed

Removed direct proof imports from the item:
`Mathlib.AlgebraicGeometry.Sites.Etale`,
`Sheaf.RingTheory.LocalGeneratingTuples`,
`Sheaf.AlgebraicGeometry.SupportLongExact`,
`Sheaf.Paper.SupportedAffineLineHomotopy`,
`Sheaf.Paper.RelativeSupportBottomDescent`, and
`Sheaf.Paper.SupportedCupFunctoriality`.
Etaleness is already available through the public frame-class interface. The remaining
imports belong to the corresponding new child results and remain transitively needed.
No old node or module is claimed pruned from the target closure. The parent node's
proof dependencies now name the three results actually combined by its Lean proof.

## Where the brief, the DAG or earlier work was wrong

No statement repair or target change. The original node already corrects the blueprint's
Smith-normal-form, strictly-local-etale-neighbourhood and constant-sheaf arguments.
This delivery follows those corrections and the unit route.

Searches found no short Mathlib replacement. The source library's regular-immersion
frame comparison uses different cohomological models and stronger smooth-over-field
hypotheses, so it does not directly prove this statement. The source ideal-sheaf
pullback lemma and Mathlib germ representation/equality and unit-shrinking lemmas are
used in the proved local chain result.

Provider interruptions resumed this same sandbox repeatedly. The dispatcher's budget
metadata changed from start 1792425878.71241 to 1792436019.9793234 between attempts;
no worker change was made to `.budget`. The original start and work were retained.
No attempt identifier is provided in the sandbox. No delivery had been started before
these resumptions; saved compile logs were checked before resuming.

## New nodes

`lem-pur-frame-local-generator-chains`: the geometric spreading part of step 2,
proved from the existing local generating-tuple theorem and Mathlib stalk APIs.
It states no cohomological equality.

`lem-pur-frame-elementary-moves`: the three elementary cohomological invariance
paragraphs, corrected steps 3--6. It applies to one move and contains neither the
local algebra reduction nor the global equality test.

`lem-pur-frame-class-local-equality`: the local equality test in corrected steps 2
and 7. Its hypothesis supplies actual local equality, so it contains neither the
algebraic chain construction nor invariance under elementary moves.

All are in the parent's chapter and unit, with the source places and search records.
No existing statement or definition changed. The preflight requires a change record
for the local elaboration attributes: `coord/changes/purity-frame-independence-elaboration.md`.
No forced adaptation is required.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
