## What changed

Extracted the original realization/comparison API into
VaryingRingOrdinaryEvaluationComparisons and its already proved module-compositor
calculation into VaryingRingOrdinaryModuleComposition. The assigned module
publicly reexports both. The extracted declarations retain their names, signatures, visibility,
definition bodies and proof bodies; only their file and blueprint attachments move. See coord/changes/E9-ordinary-evaluation-comparisons-extraction.md.
No adopted source-library file or target statement changes.

The assigned theorem chooses the original specified comparison isomorphisms.
The separate construction-normalization statement supplies the pullback and
open-extension composition laws. The final proof factors moduleAlpha and strict alpha into cartesian beta and section arrows,
then applies the proved OrdinarySquareComparison.trans to their two comparison
equations. This is a real composition of two different arrow factors.

The remaining construction normalization, cartesian comparison and section
comparison are separate public named statements with sources, full proof plans
and DAG nodes. The construction normalization contains no beta or section arrow;
the cartesian comparison contains no clopen projector; the section comparison
contains no cartesian beta. None is the assigned theorem under another name.

## Proved and sorry left

One original hole, ordinaryClopenEvaluation, is closed by a decomposition.
OrdinarySquareComparison.trans and its combination in the assigned theorem are proved. The extracted API and original
ordinaryModuleEvalG_comp have zero holes.

Three holes added, by full declaration name:

- AlgebraicGeometry.ProEtale.VaryingRing.ordinaryComparisonNormalization
  (lem-sp-varying-ring-ordinary-comparison-normalization).
- AlgebraicGeometry.ProEtale.VaryingRing.ordinaryCartesianEvaluation
  (lem-sp-varying-ring-ordinary-cartesian-evaluation).
- AlgebraicGeometry.ProEtale.VaryingRing.ordinarySectionEvaluation
  (lem-sp-varying-ring-ordinary-section-evaluation).

No other sorry occurs in delivered Lean files. One upper hole closed and three
lower holes added means net +2 holes: this is a decomposition, not a net proof
gain or a proof of the complete dependency closure.

All seven final delivery modules compile. The final main module and square-pasting
module compiled without warnings in 5.9 s and 4.9 s. The extracted module-level
proof compiled in 47.3 s. Both original direct importers were checked against the
delivery without adapting their code. Single-file checks passed at 20.7 s for
VaryingRingOpenBaseChangeEvaluation and 52.5 s for VaryingRingProperOpenPasting
(the latter with ordinary profiling enabled for diagnosis). Published-build
baselines were 20.8 s and 50.2 s. One repeated plain check exceeded the time limit;
the subsequent profile passed and its proof-phase timings matched the baseline.
The original batched consumer checks also passed the tool's compiler-time guard;
its longer reported job times include dependency setup. All temporary importer
copies and profiling options were removed from the delivery.

## No longer needed

No existing mathematical node or module is pruned. All original declared
mathematical dependencies remain used through the original constructions, the
module-compositor proof or the three remaining proof steps. The original two
public imports move to the extracted API; the assigned module publicly reexports
it through the module-compositor module. The original private Mates import moves
to the extracted compositor proof, which uses it. The new square-pasting module
needs no additional proof import beyond its public comparison API.

Searches used msearch.py with LeanFinder, Loogle, LeanSearch and grep, plus rg in
the source and Sheaf trees. The source's exact-single compositor coherence gives
a route for the construction normalization; it does not directly state the
ordinary-system to derived-constant-tower comparison. Existing
VaryingRingOpenBaseChangeEvaluation and VaryingRingClopenSectionEvaluation concern
derived evaluation to a single module category. They do not replace the present
ordinary realization comparisons. They remain in the library.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or weakened. The source constructions support the
normalization plan; the arbitrary-sequence compatibility is an agent-formulated
consequence, as the original node already says. The unit's route is preserved.
Mathematical edge checks include n=0, zero rings, changing coefficient rings,
identity and empty opens, cartesian squares and a proper/open square with a
nontrivial clopen complement. No finiteness or faithfulness on arbitrary derived
morphisms is assumed.

Direct component normalization repeatedly exceeded the compile-time limit during
kernel checking. Profiling separated the construction and module-compositor
costs. Attempts to simplify the representation did not resolve the component
application cost, so the delivery retains every original construction body and
states this strictly smaller construction-normalization step separately.
The final comparison-pasting calculation compiles independently of that concrete data.

Initial inspection mistakenly used read-only git branch/log queries, contrary
to the worker brief. They changed no repository state; subsequent inspection
used file reads and launcher tools.

## New nodes

lem-sp-varying-ring-ordinary-evaluation-comparisons attaches the original
constructions, extracted without changing bodies. It adds no hole.

lem-sp-varying-ring-ordinary-module-composition attaches the original proved
module equation and private helpers. It adds no hole.

lem-sp-varying-ring-ordinary-comparison-normalization states the two composition
normalizations, using pullback exact-single coherence and open mates in its
proof plan. It has one hole and no clopen arrow.

lem-sp-varying-ring-ordinary-cartesian-evaluation states comparison of the
cartesian beta factor. It has one hole and no section projection.

lem-sp-varying-ring-ordinary-section-evaluation states comparison of the section
factor and outgoing compositors. It has one hole and no cartesian beta.

lem-sp-varying-ring-ordinary-square-pasting attaches the proved composition of
two component comparison equations, used to reconstruct the original alpha.

The extraction change record is
coord/changes/E9-ordinary-evaluation-comparisons-extraction.md.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
