## What changed

Restored the quarantined item and proved `WeilConjectures.CompactSupportCondensedRealization.fieldRefinement_id` in
`Sheaf.Paper.CondensedCompactSupportProjection`. The proper pushforward identity is
constructed as the right-adjoint conjugate of the existing pullback identity. The
proved pullback right unit law identifies the identity refinement restriction, and
`fieldProperOpen_existsUnique` identifies the chosen arrow with the inverse proper
identity. The pullback left unit law, transported through adjunction mates, then
cancels the proper compositor.

Added proved private helpers for these mate and normalization calculations, and the
proof import `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence`.
Updated the existing node's proof and proof origin. All public statements and
construction bodies are preserved. No other module is adapted. The change record
`coord/changes/T2-condensed-refinement-local-proof-context.md` documents the new
local irreducibility attributes and the unchanged interface for consumers.

## Proved and sorry left

Closed 1 of the 7 original holes:

- `WeilConjectures.CompactSupportCondensedRealization.fieldRefinement_id`.

Added 0 holes; split off 0 statements. The six retained holes, all attached to
`def-pur-condensed-compact-support-projection`, are:

- `WeilConjectures.CompactSupportCondensedRealization.condensedProjection_comp`.
- `WeilConjectures.CompactSupportCondensedRealization.condensedProjection_id`.
- `WeilConjectures.CompactSupportCondensedRealization.fieldProperOpen_existsUnique`.
- `WeilConjectures.CompactSupportCondensedRealization.fieldRefinementApp_naturality`.
- `WeilConjectures.CompactSupportCondensedRealization.condensedProjection_refinement`.
- `WeilConjectures.CompactSupportCondensedRealization.fieldRefinement_comp`.

The identity proof uses the retained unique-normalization theorem. The restored
packet compiled through `lcompile.py` against the current published library in
35.7 seconds during this repair. The six holes are unchanged from the archived
item; they are not new split statements.

## No longer needed

None. No original import, declared dependency, node, or module is removed or withdrawn.
The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The return at head 6d65712cf15 concerned a missing item source after upstream
quarantine. Read its current `coord/rework.tsv` row and restored the complete
archived module, retaining its Lean attachment, dependencies, definitions and all
public declarations. The existing item claim is held by T2. During this repair
the shared source itself was restored byte-for-byte from the quarantine archive;
the delivered module still differs substantively by the proved identity and its
private helpers. No withdrawal or empty replacement is requested, and no archive
is deleted.

Every direct import now has live source. The old archive and current item source
are identical; the sandbox preserves them except for the already delivered
identity proof and its private proof context. The node's proof route is retained
with the additional identity calculation. The current downstream check reports
zero live importing modules; the quarantined parent
`Sheaf.Paper.CompactSupportCondensedRealization` still needs this node and its
unchanged interface. It is preserved, not pruned. The extra naturality experiment
remains in the sandbox scratchpad; it is not part of this packet.

No launcher script or shared source was edited. The retained retry markers are
`.brief2`, `.brief3`, `.brief4` and `.brief5`; their earlier work was retained.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
