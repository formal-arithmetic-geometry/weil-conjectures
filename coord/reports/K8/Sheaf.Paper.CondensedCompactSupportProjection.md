## What changed

Replaced the proof of
`WeilConjectures.CompactSupportCondensedRealization.identityScalar_flat` using
`coefficientMap_id`, `Mod.extendScalarsIsoOfEq`, `Mod.extendScalarsId`, and
`preservesFiniteLimits_of_natIso`. The composite isomorphism identifies scalar
extension along the identity coefficient map with the identity functor. Its inverse
transports finite-limit preservation. No signature, definition, or import changed.
The retained proof compiled successfully through lcompile.py against the current
published build on this resumption (19.4 seconds, exit code 0). The previously
missing `WeilConjectures.Compactification.RefinementCategory.olean` artifact is no
longer the observed blocker.

The required initial delivery dry run was started first. A subsequent tracked dry
run failed with `COMPILE FAILED (local), nothing pushed: no answer from the compile
server within 207 s (server busy or unreachable): run it again`. Two subsequent
scratch shift-proof checks also received no answer from the compile server within
209 and 194 seconds (exit code 124). These are remote-service no-answer failures,
not Lean's 60-second elaboration limit. No push succeeded or was attempted after
the failed dry run. No shared source or launcher script was modified.

The shift experiment remains confined to `scratchpad/Shift.lean` and is absent
from the delivery. Earlier compiler diagnostics identified missing shift facts
for the scalar adjunction, the proper restriction comparison, and the inverse
conjugate defining the open comparison. The scratch experiment now includes
explicit scalar-adjunction compatibility, a proof of canonical right-derived
unit compatibility adapted from the existing proved private helper in
`AlgebraicGeometry.PinnedDerivedAdjunctionShifts`, and proposed derived-comparison
helpers. The updated experiment has not been validated because both later remote
checks received no response. In particular, the final simplification in
`rightExactCompIsoShift` still needs replacement by unfolding `rightDerivedUnique`
and applying `rightDerivedNatTrans_fac`; no result from that experiment is
claimed proved. The delivery module itself still differs from the current shared
source only in the retained `identityScalar_flat` proof.

## Proved and sorry left

Closed one of the original nine holes:
`WeilConjectures.CompactSupportCondensedRealization.identityScalar_flat`.
Added zero holes; split off zero statements.

Eight original holes remain, all attached to
`def-pur-condensed-compact-support-projection`:

- `WeilConjectures.CompactSupportCondensedRealization.condensedProjection_commShift`
- `WeilConjectures.CompactSupportCondensedRealization.condensedProjection_comp`
- `WeilConjectures.CompactSupportCondensedRealization.condensedProjection_id`
- `WeilConjectures.CompactSupportCondensedRealization.fieldProperOpen_existsUnique`
- `WeilConjectures.CompactSupportCondensedRealization.fieldRefinementApp_naturality`
- `WeilConjectures.CompactSupportCondensedRealization.condensedProjection_refinement`
- `WeilConjectures.CompactSupportCondensedRealization.fieldRefinement_id`
- `WeilConjectures.CompactSupportCondensedRealization.fieldRefinement_comp`

## No longer needed

None. No original import, node, or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned node is a definition node with empty `proof` and `proof_deps`,
although the module contains nine proof obligations. Thus there is no numbered
DAG proof plan or declared proof-dependency list to instantiate for these holes.
The declaration docstrings do describe the proposed arguments.

Existing condensed bounded-constructible compactification comparisons in
`ModuleObject.Derived.LowerShriekIndependence` use finiteness coefficients,
schemes of finite type over a field, and cartesian refinement squares.
They do not directly supply the arbitrary-condensed-ring, arbitrary-refinement
normalization required by `fieldProperOpen_existsUnique`. The ringed-site
open-restriction results use a different module presentation, so an explicit
comparison would be needed before applying them here.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
