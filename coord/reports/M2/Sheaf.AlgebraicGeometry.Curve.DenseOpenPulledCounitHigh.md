## What changed

Proved `AlgebraicGeometry.IsCurve.dense_open_pulled_counit_high` with its exact original
signature. Added only proof imports: `WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport`,
`WeilConjectures.SixFunctors.OpenClosed.Complex`,
`Sheaf.AlgebraicGeometry.EtaleModulePullbackForgetNaturality`, and
`Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeBoundary`.

The new boundary module proves `AlgebraicGeometry.IsCurve.dense_open_baseChange_boundary`.
Its private, proved helper `dense_open_boundary` works componentwise on the original curve.
For each closed boundary point, Nullstellensatz and pullback pasting identify its fiber with
Spec k'. This proves finiteness and closedness of the pulled-back boundary; Nullstellensatz
on X' makes its residue fields separably closed. The target then transports the restriction
of the actual module counit through forgetting coefficients and inverse-image composition,
and applies the source library's proved finite-support cohomology theorem in degree n+2.

The original module's public imports, declaration signature and docstring are unchanged.
The parent DAG node's proof, proof_deps and proof_origin follow the actual proof. No target,
definition or existing statement changed. Read Stacks Tag 0GJA, proof and remark (c), through
its official page; the local clone does not contain the literature .tex file.

## Proved and sorry left

Proved the original single sorry:
`AlgebraicGeometry.IsCurve.dense_open_pulled_counit_high`
(lem-pbc-x2-dense-open-pulled-counit-high).

Also proved the new public theorem
`AlgebraicGeometry.IsCurve.dense_open_baseChange_boundary`
(lem-pbc-m2-dense-open-base-change-boundary), including its private geometry helper.
There are no sorries in either delivered module, and none were split off.
Both modules compile together without warnings using lcompile.py. Explicit #print axioms
for both public theorems shows only propext, Classical.choice and Quot.sound.

## No longer needed

Both existing public imports supply the original statement and remain unchanged.
The unused original proof import `Sheaf.AlgebraicGeometry.CurveCoefficientPair` was removed,
together with the proof imports associated with the five planned nodes listed below.
Removed a redundant TopologicalInvariance public import while developing the new boundary
module, because Curve.Assertions already supplies it. All four added proof imports are used.

The target proof no longer uses these planned nodes/modules:

- lem-weil-pbc-cohomology-pullback-derived-unit /
  Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit;
- lem-weil-pbc-open-closed-short-exact / WeilConjectures.SixFunctors.OpenClosed.Exact
  (only the smaller OpenClosed.Complex file is needed for the restricted counit);
- lem-weil-pbc-pullback-cohomology-long-exact-ladder /
  Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder;
- lem-weil-pbc-zero-dimensional-cohomology / Sheaf.Paper.ZeroDimensionalCohomology;
- lemma-weil-pbc-finite-direct-image-exact / WeilConjectures.SixFunctors.Finite.Exact.

These are removed as direct dependencies of this argument; this does not assert that all
are unreachable from every target or from the finite-support tool's transitive imports.
The old direct proof dependencies `lem-weil-pbc-finite-type-over-noetherian`,
`lem-weil-pbc-noetherian-finitely-many-components`, and
`lem-weil-pbc-closed-point-residue-field-base` moved into the boundary theorem's DAG route.
`def-weil-pbc-curve-setting` left the direct proof-dependency list and remains a statement
dependency supplied by the unchanged public Curve.Assertions import.
The curve-setting definition and extension-by-zero adjunction still occur in the statements
and proof. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned long exact ladder and Leray assembly were unnecessary here: the already proved
`AlgebraicGeometry.Etale.bijective_H_map_of_isIso_upperStar_map` gives precisely the needed
higher-degree implication once boundary geometry and restriction invertibility are supplied.
This node, lem-sc-iso-off-finite-set-cohomology, is recorded as Lean-closed, so its use as a
generic tool does not replace a unit route. Module inverse image forgetting naturality is
also already proved, and preserves the actual counit in the conclusion.

Edge cases checked in the construction: empty X and empty boundary, dimension zero,
reducible and nonreduced curves, arbitrary commutative coefficient rings including the zero
ring, and q=2 (n=0). No torsion, reducedness, irreducibility or constructibility is used.
LeanSearch was unavailable and is recorded as unavailable, without a mathematical verdict.
Blueprint searches for dense complements, boundary, finite sets and closed points found no
existing node giving the full pulled-back finite separably closed boundary assertion.

## New nodes

lem-pbc-m2-dense-open-base-change-boundary, in
`dag/nodes/sec-proper-base-change/`, states only geometric boundary properties, independently
of any sheaf or cohomology. Its module is
`lean/Sheaf/AlgebraicGeometry/Curve/DenseOpenBaseChangeBoundary.lean`.
The statement is fully proved, with no new sorry. Its source is the finite rational boundary
and its field extension in Stacks Tag 0GJA, proof and remark (c). Three kinds of search are
recorded from actual msearch calls. No change record is needed.

## Second reading by M2

1. Compared both delivered modules with the repository. The existing target declaration has the
same signature byte for byte; the new boundary theorem is a separately declared node. No target,
definition, or existing public statement changed.

2. Compiled both modules with `lcompile.py --all`; both pass without warnings. There are no
`sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations. The proofs use
only the permitted foundational axioms as reported by the compiler checks.

3. The boundary theorem is a genuine geometric reduction (componentwise finite boundary and
cartesian fibers), rather than a restatement of the target. Its node, source, proof steps, and
Lean declaration agree; no split-off theorem remains.

4. The target proof takes the finite-support theorem and existing inverse-image naturality and
adjunction results. Removed planned ladder and zero-dimensional cohomology dependencies are
listed above; all imports used by the proof remain. The unit route is retained through the
finite-support comparison theorem.

5. The DAG proof and `proof_deps` match the actual four-step target proof, and the new node's
fields match its theorem. Verdict: pass. Changed the report to record the removed CurveCoefficientPair proof import and every old
direct dependency (including those moved into the boundary theorem); no Lean repair was needed.
An independent leanfinder search for dense open subsets of dimension-one Noetherian schemes
found component-finiteness and dimension-zero tools, but no duplicate full boundary theorem.
Reviewed the empty-boundary and reducible-curve cases and the q=2 arithmetic step.
Read `dag/units/sk-thm-p1.json`: none of its realized statement or step nodes is pruned.
