# Q11 continuous-frame reachability maintenance

The return of a1245c021dc8 requires an unreachable flag on the new
continuous-frame helper. Stage-2 new-node validation forbids import_flags as
maintainer metadata, so the retained worker packet cannot satisfy both checks.
The parent comparison also has no DAG citers and is outside all current/former
target closures. Adding a fresh unflagged helper creates a new reach finding at
landing, even though the parent's inherited reach finding is baseline data.

Maintenance registers def-sfb-continuous-frame-module as an unstated definition
(lean: null), preserving the worker's natural-language statement, dependencies,
source, searches and provenance. It supplies import_flags: ["unreachable"] on
that node and the parent comparison. No reviewed/reviewed_lean acceptance is
fabricated. No Lean module, Lean binding, theorem statement, proof or DAG edge
is landed by this maintenance commit. The two modules remain worker delivery
content for the normal independent stage-2 review.

The helper is now an existing prerequisite. Its sandbox lean record needs a
note explaining that it has no recorded declaration yet; deliver2 overlays only
lean onto the maintainer-owned base. The worker may add the prerequisite to
stmt_deps and state it in the same delivery. Keep the metadata from this base;
do not turn the helper back into a new node or remove its unreachable flag.
The normal landing checker can clear stale flags if a future target reaches it.

No dispatcher, admission, review, delivery or landing tool was edited. No new
mathematics was done. Adjacent .maint-Q11-1792600205.bak files preserve the
original item and absence markers for the two newly created files.
