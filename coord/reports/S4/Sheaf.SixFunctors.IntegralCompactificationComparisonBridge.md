## What changed

Decomposed integralCompactificationComparisonBridge through the ordinary ringed
compact-support compositor. The Lean assembly uses the existing unique-lift
formula and faithfulness of H for equality, then the naturality of the ordinary
natural transformation for the second clause. Its signature is unchanged.

Moved the existing definitions and proved auxiliaries verbatim into
Sheaf.SixFunctors.IntegralCompactificationComparisonData and re-exported them
from the item. This permits two separate comparison statements to refer to the
data without an import cycle. Removed the old transparency-disabling options
from both item and extracted data. Updated the directIdentification attachment and
the main node's proof route. No target or existing definition changes meaning.

The new IntegralCompactificationOrdinaryComposition contains only the transport
of existing completedShriekIntegralA to the published compact-support functors.
The existing constructor in CompletedShriekCompositionLaws was found during the
library search and reused rather than duplicated. Its node is used as a tool
for this construction; its expression-realization theorem also gives part of the
semilinear obligation's stated proof. No tool_uses approvals were edited.

The constant comparison has no semilinear counit expression in its conclusion;
the semilinear comparison has no constant word or unique completed lift in its
conclusion. The original theorem needs both. Their docstrings give the generator,
adjunction and mate calculations still to formalize, with source references.
They include identity, empty-open and zero-object cases. The common-window
hypotheses are retained and their required finite-Tor and open constructibility
projections are extracted explicitly in the assembled proof.

## Proved and sorry left

This is a decomposition, not a net proof: one original hole is closed by adding
two separate model comparisons. Count: 0 of 1 holes proved outright;
1 of 1 reduced; 2 split off; local hole count increases by 1. The item itself has zero sorry.

Closed the body of
WeilConjectures.IntegralCompactificationBridge.integralCompactificationComparisonBridge
(node lem-sf-integral-compactification-comparison-bridge), including both its
equality and naturality clauses, by the complete assembly described above.

The only two delivered sorry declarations are:

- WeilConjectures.IntegralCompactificationBridge.constantOrdinaryCompactificationComparison
  in ConstantOrdinaryCompactificationComparison, node
  lem-sf-constant-ordinary-compactification-comparison.
- WeilConjectures.IntegralCompactificationBridge.semilinearOrdinaryCompactificationComparison
  in SemilinearOrdinaryCompactificationComparison, node
  lem-sf-semilinear-ordinary-compactification-comparison.

The data extraction preserves every existing auxiliary proof. No definition
contains sorry, and the unique choice in completedComparison is unchanged and
is determined by the existing Hom bijection. This delivery does not claim that
the final theorem is free of transitive sorry assumptions.

Validation: all five packet modules compile cleanly through lcompile.py. The
unmodified direct consumer was also checked with temporary profiler options: it
passed within the limit at 54 seconds, after an initial 73-second timing failure.
The timing output showed no single dominant declaration. The consumer and its
profiling options are not delivered. An isolated original-bridge baseline check
is recorded separately; no consumer signatures, definitions or proofs are changed.

## No longer needed

No module or node is globally pruned. The original generator, word and mate
obligations still serve the two model comparisons. The main proof's direct
proof_deps now list only the two comparisons, supporting data, ordinary map and
complete-coefficient faithfulness. All original public imports are retained.
The private OpenReconstructionEffectivity import is moved with its existing use
into the data module; it is not needed directly in the facade theorem module.

The following former direct proof dependencies move below the supporting data
or the two comparison statements, rather than being globally withdrawn:

- def-weil-integral-rational-qbar-compact-support
- lem-sf-open-reconstruction-effectivity
- lem-sf-cbc-compact-support-composition-limit
- lem-sf-constant-semilinear-generator-comparison
- lem-weil-pbc-constant-completion-equivalence
- lem-sf-generator-reduction-coherence
- lem-coef-derived-system-evaluation-calculus
- lem-weil-ringed-tower-pushforward-limit-comparison
- lem-sf-integral-open-reduction-comparison
- lem-sf-integral-compactification-system-realization
- lem-sf-semilinear-proper-open-mate-pasting
- lem-sf-ambient-proper-open-pasting
- lem-weil-pbc-mate-pasting

The generator-reduction coherence theorem remains available through the existing
generator-comparison route; this packet does not separately reprove it.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The original plan contains genuine compatibility
calculations, not consequences of finite-evaluation conservativity. The two
remaining statements isolate those calculations; no equality is inferred from
finite evaluation. The existing completedShriekIntegralComposition concerns
recursive expression realizations, while this item uses direct single-word
identifications and the intermediate reduction/limit counit. It does not directly
supply the comparison between those coordinates. The new semilinear obligation
states exactly this remaining identification with the existing ordinary map.

Searches used leanfinder, loogle, leansearch and grep through msearch.py, plus
local searches of both library roots and the DAG. Generic adjunction triangles
and NatTrans.naturality were found; no exact normalization theorem was found.
The latest blueprint fix-lem-exchanges Step 5 and Stacks Tags 0941, 0F7B, 0F7D,
0E48 were read. The two statements are identified as agent-formulated obligations,
not as verbatim Stacks assertions. The unit's comparison route is preserved.

## New nodes

- def-sf-integral-compactification-comparison-data records the existing data's
  acyclic supporting module. It introduces no changed mathematical construction.
- def-sf-integral-ordinary-compactification-composition records ordinaryComparison,
  which only conjugates the existing ordinary compositor by published realizations.
- lem-sf-constant-ordinary-compactification-comparison isolates compatibility of
  constant strict-word normalization with the ordinary ringed compositor.
- lem-sf-semilinear-ordinary-compactification-comparison isolates compatibility of
  the direct semilinear counit formula with that ordinary ringed compositor.

Change record: coord/changes/integral-compactification-comparison-data-S4.md.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
