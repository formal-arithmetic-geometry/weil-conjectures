## What changed

Replaced the open proof of
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_ring_scalar_mates` without changing
its signature or its public imports. The proof chooses endpoint restrictions independently of
compactification, constructs the left comparison by lifting the composite of the actual ambient
realizations through the fully faithful inclusion, proves its normalization by the map/preimage
equation, and reflects its shift equation through the faithful inclusion. It constructs the
right comparison using `mateEquiv` of inverse q and proves the counit equation using
`mateEquiv_counit`. The unit-square-counit definition of the mate proves shift compatibility.
Identity normalization remains part of the single-endpoint restriction obligation, for arbitrary
actual identity maps and composite Allowed witnesses.

Added proof imports of `RingEndpointScalarRestrictions`, `RingCanonicalScalarInvertibility`, and
`IntegralCompactSupportCoefficientComparison`. The two new modules state strictly smaller
remaining parts of the original argument. They do not assert the original assembly theorem: one
concerns a single endpoint with no operation or compactification; the other only tests geometric
invertibility and does not construct any scalar restriction, comparison datum, normalization,
shift, or counit equation. Updated the original DAG proof to match the categorical assembly and
gave each remaining theorem its own node and complete proof in words.

Validation: `lcompile.py --all` successfully compiled all three delivery modules.
The original theorem signature and every new node signature were checked verbatim;
proof dependency lists equal the unions of their proof-step uses. No profiling
options or temporary probe modules remain.

## Proved and sorry left

Closed the original direct hole in
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_ring_scalar_mates` (node `lem-sf-
ring-scalar-mates-for-realized-operations`). Its module has zero remaining holes. The private
componentwise full-inclusion lift, faithful shift-reflection, and normalized comparison helpers
have complete proofs.

Added two holes:

- `WeilConjectures.ConstructibleExceptionalCoefficients.exists_ring_endpoint_scalar_restrictions`
  in `Sheaf.Paper.RingEndpointScalarRestrictions`, node
  `lem-sf-ring-endpoint-scalar-restrictions`.
- `WeilConjectures.ConstructibleExceptionalCoefficients.ring_canonical_scalar_invertibility`
  in `Sheaf.Paper.RingCanonicalScalarInvertibility`, node
  `lem-sf-ring-canonical-scalar-invertibility`.

This is a decomposition: one original hole closed, two strictly smaller holes added, not a claim
that the complete geometric scalar theorem is now sorry-free. No existing module besides the
assigned module was changed. No definition contains a hole or is chosen from an undetermined
existence theorem.

## No longer needed

No public imports removed and no existing module withdrawn. The original finite scalar-mate,
finite-operation, finite-free completed-comparison, system-transport, normalized-reconstruction,
and integral-system-realization dependencies are retained where needed in the new nodes. They
are not direct dependencies of the categorical assembly proof, so the original node now cites
the two smaller statements and the ambient coefficient shift theorem instead. No pruning of
those geometric modules is claimed. The integral coefficient comparison module is actually used
for the ambient shift theorem; its multiplication unitor also occurs in the endpoint identity
normalization.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. Reading the dependency interfaces shows why they do not immediately
assemble the supplied theorem: the finite theorem chooses its own adjunctions, the system
theorem uses origin-system categories, and the reconstruction calculus must still be related to
the supplied full finite-Tor operations. In addition, the old `integralCoefficientComparison`
and the associated scalar-domain API require structural separatedness of X and Y, absent from
this theorem. These hypotheses were not added. The endpoint and geometric obligations retain the
original generality; the geometric proof explicitly uses actual system maps before evaluation.
The categorical assembly avoids reconstructing operations. Identity normalization is retained in
the single-endpoint theorem and does not require induction on a chosen Allowed proof. A focused
probe proved the generic identity lift, but specializing its normalization to the actual
tensorIdentity repeatedly hit a kernel timeout after explicit arguments, componentwise lifting,
stage cases and direct choice. This is retained as part of the endpoint argument, not reported
as a tool failure. The independent comparison/counit probe compiled in 18.7 seconds.
Componentwise full inclusion avoids the slow functor-category lift.

The current unit route remains unchanged. The latest blueprint and the cited Zheng Lemma 5.22,
Construction 5.25 and Propositions 5.24/5.26 were read locally. Blueprint search found no
duplicate of either smaller statement. Server LeanSearch, LeanFinder, Loogle and grep searches
and local source searches found only the generic mate and scalar APIs, not this normalized
geometric assembly.

## New nodes

`lem-sf-ring-endpoint-scalar-restrictions` records steps 1 and 5 of the original plan, including
finite literal restrictions, completed strict-tower normalization, shift-compatible realizations
and normalized identity data (original steps 1 and 5). Its only geometric object is the endpoint
W. Zero objects, identity changes, composite witnesses, ramification and residue exponent one
are covered by the stated construction.

`lem-sf-ring-canonical-scalar-invertibility` records the two geometric invertibility tests from
steps 2, 3 and 6: invertibility of the ambient proper/open scalar comparison after source
restriction and invertibility of the counit mate of any normalized q. It retains finite mates,
actual normalized-system maps, ramified cofinality and total-limit reconstruction. Faithfulness
is used only for the full inclusion, not for derived system evaluation. Both statements are
strictly parts of the original argument; all lifting, normalization, counit and shift assembly
is performed by the proved Lean helpers; the endpoint lemma retains identity normalization.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
