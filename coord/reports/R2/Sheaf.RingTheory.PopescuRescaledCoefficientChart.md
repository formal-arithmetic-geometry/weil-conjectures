## What changed

Replaced the sorry in `Algebra.exists_popescu_rescaled_coefficient_chart` by a complete
Lean reduction, without changing its signature. The reduction calls the new
`Sheaf.RingTheory.PopescuUnpaddedCoefficientChart` for the simultaneous parameter
rescaling and coefficient algebra construction, then explicitly constructs the
zero-padded parameter list and proves all powered-ideal containments.

The private, proved helpers `span_range_pow_le`, `span_range_pow_le_of_bound`,
`padded_previous_span`, `mapped_padded_previous_span` and `padded_span_pow` implement
the finite-generator bound and padding identities. The proof chooses
`n = N + d * (8 * c)`, `I₀ = H ^ n` and `K = maximalIdeal L ^ n`. It proves
`I₀Q ≤ JQ`, `K ≤ JL`, and the stronger equality `I₀L = K` using the two compatible
localization maps. All coefficient data and evaluation equalities are retained.

Updated the parent DAG proof and dependencies and added a node for the new public
construction theorem. No existing definition, statement or public import changed;
no other existing module was adapted. Local compilation of both delivered modules
passes without warnings, each well within the single-file time limit. The delivery
dry run printed OK; the second reading remains for the appointed second reader.
Scratch compilation files were removed; only the two delivered Lean modules remain.

## Proved and sorry left

Closed: `Algebra.exists_popescu_rescaled_coefficient_chart`
(node `lem-weil-pbc-popescu-rescaled-coefficient-chart`), the only original hole.
No sorry remains in the item's module or its private helpers.

Added/left: `Algebra.exists_popescu_unpadded_coefficient_chart`
(node `lem-weil-pbc-popescu-unpadded-coefficient-chart`), with whole proof `:= by sorry`.
This is a decomposition: one upper hole closed and one construction hole added,
net zero holes. The construction omits the appended zero, the powered parameter
ideal, the positive exponent witness and every powered-ideal containment. Those
parts are proved in the parent, including both quotient kernel transports.

The remaining construction follows source steps 10--13, 15 and 25. Its statement
exposes an ideal H generated locally by the d unpadded parameters and extending
to the maximal ideal of L. Its docstring and node give the parameter/Ogoma and
coefficient-enlargement induction, denominator clearing, polynomial coefficient
algebra and universe transport. It does not simply rename the parent statement.

## No longer needed

Removed the parent's direct proof imports:
`Sheaf.AlgebraicGeometry.Ogoma`,
`Sheaf.RingTheory.EssentiallySmoothBaseChange`,
`Sheaf.RingTheory.EssentiallySmoothComp`,
`Sheaf.RingTheory.PopescuEnlargeSolutionModulo`,
`Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`,
`Sheaf.RingTheory.RegularRingSmoothAscent`,
`Sheaf.RingTheory.RegularSequencePolynomialVariables`, and
`Sheaf.RingTheory.RegularSequencePowers`.
These remain dependencies of the new construction; none is claimed as pruned from
the targets' import closure. Replaced them by the proof import of the unpadded
construction and `Mathlib.Data.Fin.Tuple.Basic`. No existing DAG node or module is
eliminated from the complete route. The blueprint unit and its realized steps stay.


Old direct parent dependencies transferred to the construction (all remain in its
proof dependency route; none is pruned from the closure):

- `lem-weil-pbc-flat-local-hom-faithfully-flat`
- `lem-weil-pbc-faithfully-flat-ideal-contraction`
- `lem-weil-pbc-flat-height-formula`
- `lem-weil-pbc-field-regular-ring`
- `lem-weil-pbc-polynomial-ring-smooth`
- `lem-weil-pbc-regular-ring-smooth-ascent`
- `def-weil-regular-scheme`
- `lem-weil-pbc-localization-noetherian`
- `def-weil-pbc-finitely-presented-algebra`
- `lem-weil-pbc-regular-local-generators-regular-sequence`
- `lem-weil-pbc-regular-sequence-polynomial-variables`
- `lem-weil-pbc-regular-sequence-powers`
- `lem-weil-pbc-ogoma`
- `def-weil-pbc-regular-sequence`
- `lem-weil-pbc-popescu-enlarge-solution-modulo`
- `lem-weil-pbc-essentially-smooth-composition`
- `def-weil-pbc-essentially-smooth-ring-map`
- `lem-weil-pbc-essentially-smooth-base-change`
- `lem-weil-pbc-localization-base-change`
- `def-weil-pbc-mv-polynomial-ring`

## Where the brief, the DAG or earlier work was wrong

The extended original contracted prime H is essential. Its localization HQ need
not be the whole maximal ideal of the enlarged polynomial localization Q: new
variables can contribute additional prime relations. The construction and proof
use HQ, not a claim that d parameters generate the maximal ideal of Q.

The published source 07FJ prints n=N+dc and e=8c, then claims in step 23 that n is
large enough for containment in the e-th-power parameter ideal. That printed bound
is not valid in general (one parameter, N=c=1 gives (u²) not contained in (u⁸)).
The existing project signature already uses the larger N+d(8c); this delivery
keeps that signature and proves its bound explicitly. It does not alter any target.

The local literature source files are not populated on this machine. I read the
corresponding official source at https://stacks.math.columbia.edu/tag/07FJ.
LeanSearch returned Internal Server Error; LeanFinder, Loogle and source searches
completed and found no existing coefficient-chart construction. A compiler issue
with a quotient-kernel signature under local ring abbreviations was avoided by
writing its polynomial ring explicitly in the new signature; no tool was changed.

## New nodes

`lem-weil-pbc-popescu-unpadded-coefficient-chart`, module
`Sheaf.RingTheory.PopescuUnpaddedCoefficientChart`, states the simultaneous
rescaling and Artinian coefficient-algebra construction before zero padding and
powered-ideal comparison. Its source is 07FJ steps 10--13, 15 and 25, its original
construction dependencies are retained, and all three kinds of Mathlib search
are recorded (including the unavailable LeanSearch service). Edge cases checked:
for d=0, H localizes to zero in Q and L, the positive powers vanish, padding gives
one zero term and both kernel equalities are trivial; for c>0 and N>0 the powered
span and bound helpers apply; no claim that the new polynomial prime has dimension
d is used. There are no change records because no existing interface changed.

## Second reading by R2

1. Compared both delivered modules with the repository. The parent is the only
   existing module changed; its complete theorem signature is byte-for-byte
   identical, and all existing public imports remain identical. No definitions
   or other interfaces changed. Verdict: pass.
2. Independently compiled both modules with lcompile.py (4.4 s and 9.3 s).
   The sole sorry is the named new construction theorem. No forbidden declaration
   mechanism or hollow definition occurs. A scratch copy with #print axioms for
   both public declarations reports only propext, Classical.choice, Quot.sound
   and sorryAx. The helper proofs are kernel-checked; all witnesses in the parent
   are explicitly constructed. Verdict: pass as a decomposition, not a complete
   proof independent of sorryAx.
3. Read the unpadded statement against Stacks 07FJ steps 10--13, 15 and 25 and
   their justifications. The original flat chart has dimension d by the flat
   height formula; the extended original prime H, rather than the enlarged
   polynomial prime, is the right ideal. Checked d=0, d=1, N=c=1, the empty
   generator family, positivity of the powered exponent, unit rescaling and the
   small universe for essentially finite type coefficient rings. The new hole
   omits padding and powered-ideal comparison, both now proved in Lean, and is
   strictly a construction part of the argument. Independent LeanFinder search
   for faithfully flat Artinian subalgebra lifting returned regular-sequence
   ascent lemmas, not this construction; Loogle search for Ideal.span and
   HPow.hPow returned elementwise power bounds and span identities, not the
   ideal-power bound used here. Source searches in Sheaf and WeilConjectures
   found downstream consumers but no reusable coefficient-chart construction.
   Verdict: pass; the remaining construction is too substantial to close in
   a short second-reading repair.
4. Read the reduction from its existential conclusion downward. It retains the
   coefficient construction, proves both padding transports, proves the finite
   generator power bound using Mathlib ideal operations, and constructs I₀ and K
   with the required maps and inclusions. The old proof imports are transferred
   to the construction as its unresolved proof plan, not pruned from the closure.
   Checked dag/units/sk-thm-p1.json realized: no unit statement or step is bypassed
   and no realized node is removed. Verdict: pass.
5. Checked parent JSON differences: only proof, proof_deps and proof_origin
   change. The new node has its source, complete stepped proof, dependency union,
   searches, provenance, blueprint ancestry and verbatim Lean signature. The
   parent node follows the actual Lean reduction. Verdict: pass.

Second-reading changes: expanded the construction docstring's error correction
and denominator-clearing calculation, and explicitly listed every former direct
parent dependency transferred to the construction under No longer needed. No
Lean proof or statement needed repair. Removed the temporary axiom-check copy.
One original hole is closed and one strictly smaller construction hole is added:
net zero holes; no module is claimed pruned from the targets' import closure.
