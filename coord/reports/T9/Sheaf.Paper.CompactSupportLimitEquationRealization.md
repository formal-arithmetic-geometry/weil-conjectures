## What changed

Replaced the sole sorry in
WeilConjectures.CompactSupportLimit.compactSupportLimitEquationRealization with a Lean
assembly: output completeness makes both corners invertible; naturality of the actual
completion unit and functoriality of total limit carry the pre-limit reduction square to
the displayed corner square; cancellation and faithful scalar restriction detect equality
of parallel completed maps.

Extracted all 12 existing definitions verbatim into CompactSupportLimitEquationData and
publicly reexported them, to avoid a dependency cycle for the independently stated lemma.
The exact original declaration blocks are in the change record. No signature, definition
body or target changes. Added two theorem modules for the uncompleted site-normalization
steps and updated the parent proof plan to match the actual assembly.

## Proved and sorry left

This is a decomposition, not a net proof gain. Original holes: 1. Item holes now: 0.
Closed the body of WeilConjectures.CompactSupportLimit.compactSupportLimitEquationRealization
(node lem-pur-compact-support-limit-equation-realization) relative to the two named steps.
Added 2 holes, each the whole body of a public theorem in its own module:

- WeilConjectures.CompactSupportLimit.completeIntegralConstantRestriction
  (lem-pur-complete-integral-constant-restriction).
- WeilConjectures.CompactSupportLimit.compactSupportPathReductionSquare
  (lem-pur-compact-support-path-reduction-square).

Both are strictly parts of the original argument. The scalar theorem has no expression,
path, limit equation or refinement hypotheses; it transports completeness and Hom
faithfulness to the fixed small-site coordinates. The reduction theorem is an equation
before applying total limit, with no assertion of corner invertibility or cancellation.
The data module has 0 holes. Net holes closed minus added for this packet: -1.

## No longer needed

No mathematical dependency or module is withdrawn. The three original public imports move
to the data module and remain transitively public. The scalar, generator and context constituents
remain in the two new obligation nodes; the upper assembly needs their two precise
conclusions. Its original long list of proof dependencies is replaced by those obligations
and the data definition node. This is principally redistribution.

The old direct dependency lem-cbc-complete-proetale-refinement-exchange-coherence
(Sheaf.Paper.RefinementExchangeCoherence) is not needed to prove this universal transport
implication: it supplies examples of equal strict paths to which the theorem can later be
applied. It does not prove the scalar or pre-limit square. The old direct dependency
prop-weil-pbc-rlim-functoriality (Sheaf.Paper.CompletedRlimFunctor) is not needed as a
separate theorem application: total limit is already a functor in the definitions and
Mathlib supplies map_comp. Both modules remain transitively imported by existing public
interfaces; this delivery does not withdraw either or claim that it leaves target closure.

No unused proof import remains in the assembly. No finite-evaluation faithfulness or
commutation of arbitrary pullback with inverse limits is asserted.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan correctly separates coefficient transport,
reduction-level normalization, total-limit functoriality and cancellation, but the available
Lean dependencies do not expose the exact site-specialized reduction square and scalar
completeness facts as ready-to-apply declarations. Their construction involves the scalar
normalization, strict diagram realization and refinement mate interfaces. Those precise
glue obligations are now independently stated, with the original proof steps and sources.

Edge checks: zero objects, identity paths, empty sites, supplied compactification expansion,
and inverse orientation all preserve the stated equations. The scalar theorem assumes
completeness only via finiteTorConstructibleIntegral; it does not assert ambient faithfulness.
All intermediate-domain hypotheses and the original typed Path syntax are unchanged.

## New nodes

lem-pur-complete-integral-constant-restriction records parent Steps 1 and 9, scalar
completeness and injectivity of the restricted Hom map; its source is Stacks 099I/099L/099N
and the existing fixed coefficient and small-site comparisons.

lem-pur-compact-support-path-reduction-square records the pre-limit part of parent Steps
3--8, keeping the actual specified maps and the complete strict-tower equality.

def-pur-compact-support-limit-equation-data indexes the unchanged extracted definitions;
it introduces no new construction or theorem assumption.

Change record: coord/changes/T9-compact-support-limit-equation-interface.md.

Validation before delivery: exact text comparison confirms the 12 data declaration blocks
are byte-for-byte identical to their original bodies and signatures. Every changed node has
proof_deps equal to the union of uses, all cited node ids exist, and the new graph edges
introduce no cycle. Remote Lean compilation and delivery preflight results are recorded below.

The first remote pass compiled CompactSupportLimitEquationData (39.5 s),
CompleteIntegralConstantRestriction (34.3 s) and CompactSupportPathReductionSquare
(47.1 s). It identified a projection issue in the main proof: IntegralDomain is a
recursive definition, so its first conjunct needs cases on the expression. Added
a fully proved private integralDomain_output helper; no public signature or data
body changed. The corrected main module is being checked separately.

The corrected projection helper passed. The next single-file check took 3.1 s and
found a rewrite transparency mismatch between completion and the reduction/limit
composite. Replaced that concrete rewrite with a fully proved private categorical
limit_square helper, specialized to the exact functors. This changes only proof
organization and does not alter the definitions or introduce an extra assumption.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
