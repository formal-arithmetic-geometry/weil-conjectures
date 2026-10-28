## What changed

Replaced the proof hole in `Sheaf.Paper.NativeProperScalarMateBoundedBelowRestricted`
by an argument using the existing integral localization comparison and bounded proper
finite-field-to-algebraic-closure pushforward comparison. The proof chooses one lower
bound, transports it through an additive exact coefficient equivalence, preserves it
through the exact integral localization, and applies both existing comparison theorems.
An isomorphism in the arrow category transfers invertibility back to the actual native
mate; restriction then preserves it. The item's signature and public imports are unchanged.

Added `Sheaf.Paper.NativeProperScalarMatePresentation`, containing one structural
presentation statement: for arbitrary morphisms and arbitrary unbounded complexes, the
native mate is isomorphic as an arrow to the two successive condensed coefficient mates
transported through additive exact equivalences. Its algebraic-closure coefficient is
the published finite-subextension-valued `Profinite.padicAlgClRingObj`, as required
by the native locally finite realization. It assumes neither properness nor
boundedness and asserts no invertibility of either mate. The unproved part is therefore
the coefficient presentation and mate identification, rather than the proper/bounded
invertibility assertion again. The auxiliary constructions are in the zero-hole module
`Sheaf.Paper.NativeProperScalarMateData`: the two derived scalar functors and their
actual composite, together with direct aliases to the canonical module closedness
and symmetry and proved flat-resolution, exactness and tensor-coherence properties.
Naming these canonical constructions keeps each module below the compilation limit. No data are chosen from the new unproved theorem: its witnesses are used only
inside the item's theorem proof.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.LocallyFiniteAdicCompactSupport.native_proper_scalar_mate_bounded_below_restricted`
(node `lem-sf-native-proper-scalar-mate-bounded-below-restricted`). The item has zero remaining
holes. Added one hole:
`WeilConjectures.LocallyFiniteAdicCompactSupport.native_proper_scalar_mate_presentation`
(node `lem-sf-native-proper-scalar-mate-presentation`). This is a decomposition: one hole
closed and one structural hole added, with net reduction zero among these statements. The analytic
invertibility results are existing proved declarations, not newly assumed statements.

## No longer needed

No existing module or mathematical dependency is pruned. No import was removed.
The original continuous realization, locally finite coefficient realization,
internal/section transport and pasted-mate dependencies now belong to the new structural
node. The item's proof directly uses the new node, localization exactness, and the two
existing invertibility results. The unit's statement and route are retained.

## Where the brief, the DAG or earlier work was wrong

The original single proof step did not provide the Lean identification between the
completed section-module mate and the successive condensed mates. The available
localization and bounded proper pushforward theorems already prove invertibility once
this identification is supplied. The delivery separates this structural identification
from those two mathematical results instead of restating invertibility under a new name.

The presentation was tested conceptually on identity morphisms, empty schemes and zero
complexes: only coefficient equivalences, balanced scalar associativity, and adjunction
unit/counit equations enter, so no nonemptiness, properness or cohomological bound is
needed for this structural statement. All boundedness requirements remain in the proved
assembly. No target statement, shared definition, existing consumer, or upstream source
module is changed.

A raw traversal of metadata, including historical fields of finished nodes, encountered a cycle at
`lem-pc-ring-hom-extension-differential` and a missing deeper dependency
`lem-weil-pbc-site-comparison-finite-level`. I did not alter that unrelated metadata.
Every immediate dependency of the new node exists, and traversing those dependencies
introduces no cycle through this item or the new node.

## New nodes

`lem-sf-native-proper-scalar-mate-presentation`, in
`dag/nodes/sec-six-functors/lem-sf-native-proper-scalar-mate-presentation.json`, states the
unbounded arrow comparison and records the coefficient-ring, completion, module transport,
and pasted-mate steps. Its source is the presentation/pasting part of the original node,
Bhatt--Scholze Lemma 6.8.2 and Remark 6.8.15, and the current blueprint scalar direct-image proof's formal-properties paragraph.
HRS Lemma 5.3 supplies the analytic boundedness argument already proved in the imported
comparison modules; its equation (5.4) is a colimit comparison, not a mate-pasting identity.
Mathlib searches found abstract mate-pasting and arrow-isomorphism lemmas, but no concrete
completed-to-native coefficient-presentation comparison. The proved
`ScalarDirectImageMateCoherence` supplies scalar-composition coherence for its internal
model; it does not identify the completed/native coefficient presentations in this item.
No change record is needed:
only the item, its node, and the two new modules and their nodes are changed.
The blueprint ancestor tool returns `None` for the current module-named creation chain;
the new node records that explicitly and retains the inherited paper anchor rather than
claiming its split-off parent is itself a blueprint node.

`def-sf-native-proper-scalar-mate-data`, in
`dag/nodes/sec-six-functors/def-sf-native-proper-scalar-mate-data.json`, records
the canonical successive scalar functors and their actual mate composite. All definitions
are explicit constructions from published definitions; all supporting coherence and
exactness theorems are proved. This module adds zero holes.

Validation: all three modules compiled in import order with transparency checking
enabled, within the 60-second limit per file (approximately 32, 10 and 28 seconds).
The diagnostic profiling settings were removed before delivery.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeProperScalarMateBoundedBelowRestricted": "926bfae07ee305a9bececeaee21fa1a6ef01af68", "Sheaf.Paper.NativeProperScalarMateData": "3d3577b7f1500d617ef3454361b3b7ec119d715b", "Sheaf.Paper.NativeProperScalarMatePresentation": "c485030c78baf16ef8cdbb2ca99861d9947bde10"}, "results": {"Sheaf.Paper.NativeProperScalarMateBoundedBelow": {"hash": "0714c8682710fb32488a8bbda3cf9d0980e7e183", "status": "OK"}}, "seconds": 45, "time": "2026-10-28T08:30:39+0800", "transitive": 0, "version": 1}
```

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
