## What changed

Proved `AlgebraicGeometry.HilbertSamuel.jet_level_finite_lengths` in
`lean/Sheaf/AlgebraicGeometry/JetLevelTopologyReachableDcc.lean`, with its signature
unchanged. The proof installs local Noetherianness using the existing Mathlib theorem
`LocallyOfFiniteType.isLocallyNoetherian`. For each stalk R and maximal ideal m,
m^(q+1) is proper, so its quotient is nontrivial. A prime in the support of the
quotient contains m^(q+1), hence m by primality, and equals m by maximality. The
existing proved theorem `Module.length_eq_nat_of_support_subset_maximalIdeal`
therefore identifies the length with a natural number, which is not infinity.
This implements the finite-length part of node step 1 without adding lemmas.

The remaining three declarations retain their original statements and `sorry`
bodies. Removed nine unused private proof imports. All public imports and
public declaration signatures are unchanged. No shared definitions, consumers,
source-library declarations or DAG statements were changed.

## Proved and sorry left

Closed one of the original four holes:
`AlgebraicGeometry.HilbertSamuel.jet_level_finite_lengths`.
Added zero holes and split off zero statements.

The three remaining holes, all with node
`lem-trf-jet-level-topology-reachable-dcc`, are:

- `AlgebraicGeometry.HilbertSamuel.jet_level_presentations`.
- `AlgebraicGeometry.HilbertSamuel.jet_level_topology`.
- `AlgebraicGeometry.HilbertSamuel.jet_level_reachable_diagrams_dcc`.

The proved declaration follows the existing node's argument; its dependencies
are the finite-type/Noetherian Mathlib leaf and the proved support/length lemma.
The other three declarations are untouched, rather than replaced by new holes.

## No longer needed

The following private imports were unused by the completed proof and removed:

- `Sheaf.AlgebraicGeometry.JetDiagramHilbertControl`.
- `Sheaf.AlgebraicGeometry.CoordinateSubspaceBlowupCharts`.
- `Sheaf.SecTraceFormula.SmoothCenterBlowupGeometry`.
- `Sheaf.AlgebraicGeometry.StrictTransformFlatBaseChange`.
- `WeilConjectures.LinearAlgebra.NonzeroMaximalMinorOfInjective`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `Mathlib.Algebra.Module.FinitePresentation`.
- `Mathlib.RingTheory.FiniteType`.
- `Mathlib.LinearAlgebra.TensorProduct.RightExactness`.

No mathematical DAG dependency is withdrawn: these inputs remain in the
recorded plan for the three open declarations, and can be imported when those
proofs use them. The unit route is unchanged. No module withdrawal is requested.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found in the finite-length argument. The original
module imported several planned proof dependencies before any proof used them;
this delivery retains only the two private imports used by the completed proof.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
