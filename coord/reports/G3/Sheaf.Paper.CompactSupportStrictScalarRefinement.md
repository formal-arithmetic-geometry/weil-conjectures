## What changed

Proved scalar_properOpen_gamma by transposing both sides under the proper
adjunction, applying scalar_properOpen_alpha, and using the prescribed geometric
counit transposes. The abstract calculation is a proved private helper.

Proved supportRefinementIso_coherence by transporting the existing normalized
refinement identity and composition equations through supportModel. The proof
first establishes equalities of natural transformations, then evaluates at M and
compares inverse maps. This avoids expensive conversions between image and
compositionF after evaluation. Preserved the preceding V7 proof of
supportRefinement_isIso. Added a local irreducibility attribute for support to
avoid unfolding its large construction while checking these proofs.

All public statements, definition bodies and imports are unchanged. New helpers
are private and proved. No source-library file is changed.

## Proved and sorry left

Closed two of eight existing holes, both attached to
lem-pur-compact-support-strict-scalar-refinement:

- WeilConjectures.PurStrictScalar.scalar_properOpen_gamma
- WeilConjectures.PurStrictScalar.supportRefinementIso_coherence

Six existing holes remain, all attached to the same node:

- WeilConjectures.PurStrictScalar.scalar_clopen_projection
- WeilConjectures.PurStrictScalar.scalar_properOpen_alpha
- WeilConjectures.PurStrictScalar.scalar_compactification_composition
- WeilConjectures.PurStrictScalar.scalar_refinement_origins
- WeilConjectures.PurStrictScalar.compactSupportStrictScalarRefinement
- WeilConjectures.PurStrictScalar.compactSupportStrictScalarRefinementCoherence

No holes added and no split-off statements. The gamma proof uses the existing
scalar_properOpen_alpha theorem, whose hole is reported above.

## No longer needed

No dependencies, nodes or modules are withdrawn. The existing private import of
RefinementExchangeCoherence supplies the normalized equations; the public
imports already provide the mate and transpose APIs. No additional imports are
needed. Unused exploratory helpers and the cofilteredness import were removed.

## Where the brief, the DAG or earlier work was wrong

The initially read source contained nine holes. During this session the shared
source updated to the V7 landing, which independently closed
supportRefinement_isIso and removed unused imports. This delivery preserves that
landing and uses the current eight-hole baseline.

No statement correction or definition repair is needed. The unit route is
unchanged. A candidate proof of the final coherence theorem elaborated all its
clauses, but checking the implicit support-limit conversions exceeded the file
limit. It is not delivered as a proof; the existing sorry remains unchanged.
Empty opens and zero inputs require no extra cases in the two delivered proofs:
the arguments use only adjunction identities, functoriality and inverse maps.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
