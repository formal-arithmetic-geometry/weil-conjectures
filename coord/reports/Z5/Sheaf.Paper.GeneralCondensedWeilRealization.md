## What changed

Restored lean/Sheaf/Paper/GeneralCondensedWeilRealization.lean from the exact
quarantine path in coord/rework.tsv. Repaired the recorded obsolete
WeilBoundedConstructibleOfEnd reference in Target to the current upstream
WeilBoundedConstructible name. The latter is still the IsoAlgebra category of
bounded constructible pullback along the model endomorphism, with the same
coefficient ring and hypotheses. Added public CompactCohomology and Stalk imports
so the Data signature exposes the actual published global and local operators.
All archived imports, declarations, other bodies, and the theorem statement remain.
The item's node retains its attachment and dependencies; its Lean note records
this restoration. Change record:
coord/changes/Z5-general-condensed-weil-upstream-api.md.

The repaired file compiled remotely in 28.1 seconds with exit code zero before
retaining the additional original Statement reexport. The delivery tool validates
the final version and declaration axiom probe. Active and quarantined consumer
searches found no Lean importers; the supported downstream --allow-missing query
also found zero. No consumer adaptation is required.

## Proved and sorry left

This is the assigned rework/API repair, not a proof or decomposition. Holes closed:
zero of one. Holes added: zero. One original sorry remains, exactly the whole proof
of WeilConjectures.GeneralCondensedWeil.general_condensed_weil_realization
(lem-zl-general-condensed-weil-realization). Its full thirteen-step proof docstring
and DAG proof plan remain unchanged. No data are selected from an unproved mere
existence theorem, and no definition contains sorry.

## No longer needed

None. No archived import, declaration, node, module, or planned dependency is
withdrawn. In particular the quarantined module is restored rather than deleted,
and its parent lem-zl-finite-stage-categorical-trace remains a valid consumer of
the node. The proof route and unit route are retained.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a theorem-proving item, but this dispatch is marked
repair and coord/rework.tsv records a quarantined API failure. The archive used
the old upstream name WeilBoundedConstructibleOfEnd. The current definition in
WeilConjectures/WeilObject/BoundedConstructible/Defs.lean is
WeilBoundedConstructible, still for arbitrary endomorphisms. The actual
CompactCohomology.globalOperator and Stalk.stalkFrobenius signatures match every
field after this name repair, as checked by Lean. No theorem is claimed proved.
The empty coord/returns/Z5.md contains no additional numbered repair points.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
