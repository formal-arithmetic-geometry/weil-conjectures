## What changed

Proved `AlgebraicGeometry.ProEtale.SemilinearProperOpen.systemCompatibleCompositorNormalization`
from a strictly smaller finite evaluation lemma and existing proved library facts.
The proof obtains the geometric triangle from
`exists_compatible_compactification_triangle`, checks qcqs and Noetherian hypotheses,
produces identity-scalar origins separately at every level, and proves invertibility
by cancelling the canonical support isomorphisms in the finite equation and using
joint conservativity for invertibility. It never detects equality of system maps by
evaluation and imposes no common cohomological or Tor interval.

Moved the ten unchanged plain definitions to
`Sheaf.Paper.SystemCompatibleCompositorData`, publicly reexported by the original
module. This permits the new finite-word statement without an import cycle.
The module, namespace, signatures, attributes and defining terms are recorded in
`coord/changes/K6-system-compositor-data.md`. No consumer adaptation is needed.
Existing proved private helpers `scalar_origin` and `system_isIso_of_evaluations`
are used through `import all Sheaf.Paper.SystemProperOpenInvertibility`; neither
appears in a public signature or a definition body.

## Proved and sorry left

Original item: one hole. Closed the body of
`AlgebraicGeometry.ProEtale.SemilinearProperOpen.systemCompatibleCompositorNormalization`.
Added one hole:
`AlgebraicGeometry.ProEtale.SemilinearProperOpen.systemCompositorFiniteWordEvaluation`,
node `lem-pur-system-compositor-finite-word-evaluation`.
This is a decomposition (one hole closed, one added), not a net proof gain.
There are zero holes in the original item or in the shared data module, and exactly
one in the delivery. No definition contains a hole. The finite lemma has a supplied
bounded-below identity-scalar origin and a fixed geometric triangle; it asserts only
the specified finite map equality, without geometric existence, origin existence,
constructibility-domain invertibility or any system-map equality claim.

## No longer needed

Removed these original private proof imports from the item:
`Sheaf.Paper.UnboundedProperOpenInterchange`,
`Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`,
`Sheaf.Paper.ProperOpenCoefficientMate`,
`Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`,
`Sheaf.AlgebraicGeometry.FiniteClopenMateSiteTransport`,
`Sheaf.AlgebraicGeometry.SemilinearCompositorCoherence`,
`Sheaf.Paper.FiniteCompactSiteCoherence`, and
`Sheaf.Paper.OpenFiniteConstructibilityInterval`.
The finite-word node still uses the unbounded interchange, proper/open coherence,
coefficient mate, finite mate transport and finite compact-site coherence as its
proof plan, so these are not claimed as globally pruned modules.

The item no longer needs `lem-sf-open-finite-constructibility-interval`: invertibility
follows from the finite equation itself, without establishing constructibility of
`J_j M`. It also does not use `lem-sf-semilinear-compositor-coherence` or
`lem-weil-pbc-locally-noetherian-quasi-separated`; qcqs follows directly from the
separated structure maps. It needs no independent ambient-over-field construction:
Noetherianity ascends along the existing proper maps. Its former public imports
are preserved through the shared data module. No library module is withdrawn.
The corresponding obsolete top-level tool approvals are removed from the item:
`lem-weil-pbc-locally-noetherian-quasi-separated`,
`lem-weil-pbc-proper-fp-permanence`,
`lem-sf-open-finite-constructibility-interval`,
`lem-cbc-finite-clopen-mate-site-transport`, and `thm-sf-comp-composition`.
The finite mate transport remains in the new node's proof plan.
The new lemma imports only its public shared-data interface; its proof remains
the named split-off hole, so no unused private proof imports are retained.

## Where the brief, the DAG or earlier work was wrong

The existing declarations give the geometric construction and the mate equation,
but do not directly state the full evaluation identity after both compositors.
The new node isolates that genuine remaining Steps 4--6 calculation. The old
route established open constructibility just to prove invertibility; finite-word
normalization and joint conservativity already provide it. The published data and
theorem shared one module, requiring an unchanged-data module move to state a
noncircular intermediate lemma. All original theorem hypotheses and conclusions
are retained. Identity and empty-open cases are included in the new lemma's proof
in words and use the same canonical comparison maps.

## New nodes

`lem-pur-system-compositor-finite-word-evaluation` states the exact evaluation
identity at a supplied origin for the actual system word, through the prescribed
finite transports and the supplied three compactifications. Its proof is the
parent's Steps 4--6: normalize gamma, transport its finite mate to the open-adjunct
interchange, compare both compositors by adjunction transpose normalization, and
apply finite-site tower paste. Every lower dependency already has a declaration.
Source: Stacks 0F7J, the four displayed identifications, and Zheng Lemma 4.10.
The only change record is `coord/changes/K6-system-compositor-data.md`.

Read-only graph verification found an existing descendant cycle involving
`lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent`. The new finite-word node does
not reach its parent, and the delivered Lean import graph has no cycle.
The original signature and all ten moved defining declarations were checked
byte-for-byte against the source.

Validation: the full main proof compiled in 8.0 s, with kernel checking below one
second. The shared-data and finite-word modules previously compiled within 60 s
(51.3 s and 54.6 s on the set check). The slow full-proof checks were diagnosed as
kernel conversion through local coefficient-system aliases; using the literal
coefficient expressions removes that cost. The source domain is unfolded explicitly
before taking constructibility projections, and finite isomorphism cancellation
uses direct term checking rather than rewriting across compactification endpoints.
All temporary profiling and heartbeat options have been removed. The final delivery
runs compilation and the complete packet checks again.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
