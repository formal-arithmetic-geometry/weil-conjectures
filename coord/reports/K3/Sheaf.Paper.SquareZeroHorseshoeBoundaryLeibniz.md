## What changed

Proved `AlgebraicGeometry.square_zero_horseshoe_boundary_leibniz` in
`Sheaf.Paper.SquareZeroHorseshoeBoundaryLeibniz` without changing its signature,
visibility, universe, or docstring. Added two proved private helpers:
`common_lifts` intersects the two lifting covers, and
`snake_boundary_eq_triangle` cancels the transports in the existing
`rightDerived_triangle_connecting` theorem.

The main proof chooses the canonical comparison from `cechH1Map_natural`, applies
`boundary_cech_compatibility` to the three sections on the same cover, proves the
cycle equality sectionwise by ring algebra and `hlift`, and passes to homology
using naturality and additivity. The boundary comparison then identifies this
with the specified snake map. Updated only the node's proof, proof_deps and
proof_origin to record this route. All added imports are proof-only. All options
are local to individual declarations; no instance or interface is changed.

Read Stacks Tag 0B8S online because the literature sources are absent on this
machine. The proof follows its common-cover product computation. It uses the
library's corrected difference convention t1-t0 uniformly. No existence witness
is used to define data: the covers, lifts, comparison and cocycles are eliminated
only while proving a proposition, and the action and boundary remain inputs.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.square_zero_horseshoe_boundary_leibniz`
(node `lem-sc-square-zero-horseshoe-boundary-leibniz`).
Both private helpers are fully proved. No sorry remains in the delivered module,
no hole is added, and no statement is split off. This is a proof from the existing
stated dependencies, including `boundary_cech_compatibility`, whose proof is
still sorry in the repository; it is not a claim that the entire imported
cohomology theory is axiom-free yet.

Local compilation checks the complete proof with no errors or warnings. Empty
spaces/covers, zero kernels and split extensions are not excluded. The cover
argument uses arbitrary suprema; the zero-kernel and split cases need no separate
choices or hypotheses. Sectionwise injectivity follows from hS, and square-zero
is retained in the unchanged signature, although the given hlift equation makes
its separate use unnecessary in this identity.

## No longer needed

Removed the proof-only imports `Sheaf.AlgebraicGeometry.BoundaryCechLocalLifts`
and `Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor`.
The wrapper theorem/node `lem-sc-boundary-cech-local-lifts` is not used: its
lower, uniform theorem `lem-sc-boundary-cech-compatibility` accepts the same
canonical comparison supplied by naturality, avoiding the wrapper's separate
existence and injectivity assertions. No injectivity of the comparison is needed.

`lem-weil-pbc-horseshoe-delta-functor` is no longer a direct proof dependency;
its module remains a dependency of the retained triangle-comparison theorem.
`lem-weil-pbc-derived-functor-map-via-lift` is not needed as a separate direct
step; its generic machinery is encapsulated by the existing triangle comparison.
Retain the existing public imports because the unchanged signature needs their
algebra sheaves, underlying-module construction, derived global sections and
homology boundary types. The Čech-complex definition and short-exactness node
remain used in the elementary cycle calculation.

The added generic tool `lem-sc-p1-right-derived-triangle-connecting` is filed
in the Picard-duality unit but merely compares two presentations of the same
connecting map; it replaces no unit-level mathematical argument. The item's
unit `sk-thm-curveestimate` has no realized proof steps, and its realized
statement `thm-sc-proper-cohomology` is not bypassed.

## Where the brief, the DAG or earlier work was wrong

The original final step cited the horseshoe delta-functor theorem and resolution
map computation, but those statements alone do not identify their boundary with
`moduleCohomologyBoundary`, which is defined by the derived triangle. The
existing `rightDerived_triangle_connecting` theorem supplies precisely that
missing comparison and is now used explicitly, including its eqToHom transports.

The supplied lift-action hypothesis already says how multiplication acts on
kernel sections, so no square-zero-product lemma or construction of a quotient
action is required. The signature and existing docstring are preserved. The
existing sign-correction record `boundary-cech-local-lifts-sign.md` was read;
this proof uses the corrected t1-t0 convention in all three applications.

Searches: local rg found only the parent derivation theorem (which imports this
item, so cannot be used), the quotient-action theorem, and tensor-boundary
variants. LeanFinder returned no applicable sheaf-boundary Leibniz theorem;
Loogle provided the standard homology-class naturality API. Logged Mathlib grep
found cyclesMap infrastructure; LeanSearch was unavailable (HTTP Internal
Server Error), not evidence of absence. No new node or forced adaptation is
needed.

## Second reading by K3

1. **Statements and interfaces.** I compared the delivered module with the
repository version. The theorem signature, visibility, universe parameters,
hypotheses, and conclusion are byte-for-byte unchanged. The existing node
statement and Lean record match that declaration; no target statement or
definition was altered.

2. **Proof and axioms.** The module compiles with `lcompile.py` and contains no
`sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow
definition. The proof uses the imported named results and elementary ring and
homology identities. The delivery preflight axiom probe timed out at its
60-second per-file limit, but compilation succeeded; this is an elaboration-cost
limitation, not a proof error. The source contains no explicit non-permitted axiom.

3. **New or split statements.** No statement was split off and no new node was
added. The two private helper theorems are complete proofs of local propositions,
not public interface lemmas. Their cover construction and triangle comparison
use the supplied hypotheses directly and cover empty, zero, and split cases.

4. **Shortest route and pruning.** I checked the imported declarations and the
DAG route. The proof uses the existing Cech compatibility, naturality, local
lifting, and right-derived triangle comparison results. The removed local-lifts
wrapper, horseshoe delta-functor theorem, and separate lift-map dependency are
genuinely unused; retained imports are needed by the signature or proof. The
unit route is preserved: the existing realized Cech and triangle steps remain in
use, and no unit-level result is bypassed.

5. **DAG agreement.** The node's `proof`, `proof_deps`, and `proof_origin`
describe the actual common-cover calculation and derived-boundary identification
in the module. The closed-hole count agrees with the file: the sole original
theorem is proved, with no holes added.

I changed only this report section after reading; no Lean source, statement, or
DAG content was changed during the second reading.
