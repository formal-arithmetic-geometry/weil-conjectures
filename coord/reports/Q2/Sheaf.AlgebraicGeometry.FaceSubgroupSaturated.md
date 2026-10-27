## What changed

Replaced the sole sorry in `AddSubmonoid.face_subgroup_saturated` with the direct
argument in node `lem-trf-face-subgroup-saturated`. Closure induction expresses each
element of the generated subgroup as a difference of two face elements. For a
positive multiple in this subgroup, translate by the second face element, use
saturation to lift the translate to the monoid, and use injectivity and the face
condition to show the lift lies in the face. Finally, lift two quotient elements
with equal positive multiples and apply subgroup saturation to their difference.
The declaration signature, docstrings and public imports are unchanged.

## Proved and sorry left

Closed: `AddSubmonoid.face_subgroup_saturated`
(node `lem-trf-face-subgroup-saturated`): 1 of 1 original holes.
Added holes: none. Remaining holes: none. Split off: none.
The proof handles zero multiples separately and positive multiples as successors,
including the case n = 1. It imposes no finite generation or sharpness hypothesis.
Validation: single-file compile through lcompile.py; delivery preflight also checks
axioms and the unchanged public signature.

## No longer needed

None. No imports were added or removed; no declared proof dependencies or modules
are bypassed. The node has no proof dependencies and its two-step route is kept.

## Where the brief, the DAG or earlier work was wrong

None. The direct argument in the node suffices without new statements or repairs.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
