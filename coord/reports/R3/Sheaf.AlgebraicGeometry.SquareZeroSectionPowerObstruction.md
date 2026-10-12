## What changed
The existing theorem `exists_square_zero_section_power_obstruction` retains its exact
signature. Its quasi-coherence conjunct is now proved using upstream closed-immersion
pushforward, kernel, invertible-tensor, and pullback results, with the adjunction comparison
between the concrete tensor pullback and Mathlib pullback. The remaining obstruction-and-lifting
conjunct is stated in the new module
`Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLiftingCriterion` as
`square_zero_section_power_obstruction_core`.

Removed the redundant new theorem `square_zero_section_power_obstruction_qcoherent` and its
node. Expanded the remaining theorem's source proof, made its node self-contained, replaced
unverified search claims with actual second-reader searches, and updated the parent node's
proof route. There is no change to any existing definition or declaration signature.

## Proved and sorry left
Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_square_zero_section_power_obstruction` by proving
its quasi-coherence conjunct and applying its remaining obstruction-and-lifting conjunct.
Added one hole:
`AlgebraicGeometry.Scheme.Modules.square_zero_section_power_obstruction_core`, node
`lem-sc-square-zero-section-power-obstruction-core`, in the new lifting-criterion module.

This is a **decomposition**, not a proof of the graded-boundary argument: one existing hole
closed and one new hole added, net zero. The parent still depends on `sorryAx` through the
core. The first worker's additional quasi-coherence hole has been removed; quasi-coherence
needs no new theorem or hole. No definition contains `sorry`; no new data definition or
arbitrary witness construction was introduced.

## No longer needed
The following imports are removed from the parent module's direct imports:
`Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor`,
`Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge`,
`Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated`,
`Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient`, and
`Sheaf.Paper.BoundaryDerivationSquareZero`.

The corresponding old proof dependencies
`lem-weil-pbc-invertible-pullback-tensor`,
`lem-weil-pbc-affine-morphism-cohomology-edge`,
`lem-weil-pbc-closed-immersion-pushforward-annihilated`,
`lem-weil-pbc-closed-immersion-unit-quotient`, and
`lem-sc-boundary-derivation-square-zero`, together with
`def-sbc-ideal-sheaf-powers`, move to the core's unfinished proof plan. They are no longer
used directly by the parent's proof but remain needed by the retained boundary/lifting
argument, with their modules imported in its new module. Thus no library module is pruned
from the targets' import closure. The original public imports remain unchanged:
ClearDenominators really is required by the signature because it defines `tensorPowSection`.

## Where the brief, the DAG or earlier work was wrong
The first report described an uncompleted conjunction decomposition as a complete proof.
The two new holes increased the hole count. The quasi-coherence node was unnecessary:
existing upstream declarations prove this component. The parent DAG was not updated to
match the assembly proof; the new nodes' statements referred to the parent rather than
being self-contained; the core's word proof was only a summary; the search assertions were
not backed by this item's actual searches; new statements were placed in the old module
instead of a new module. These issues are corrected.

The difficult construction of graded boundary maps, its naturality, and exactness are still
open. The retained core is exactly the remaining conjunct, strictly omitting the independent
quasi-coherence assertion now supplied by a real proof; no claim of net progress or of
having proved those geometric steps is made.

## New nodes
`lem-sc-square-zero-section-power-obstruction-core` is the source's boundary-and-power-lifting
criterion without the separately proved quasi-coherence assertion. Its natural-language
statement spells out X, Z, j, I, L, n, s, F, the H1 action, the lift and its tensor comparison;
its complete word proof and planned dependencies are inherited from the original argument.
The Lean declaration is in
`lean/Sheaf/AlgebraicGeometry/SquareZeroSectionPowerLiftingCriterion.lean`.
No change record is needed: no existing public signature, definition or public import changed.

## Second reading by R3
1. Compared the original and delivered modules using `diff`, then compared the exact
   substring from the original theorem keyword through its signature: byte-for-byte equal.
   No original declaration is removed and no hypotheses, conclusions, definitions or public
   imports change. The redundant additions were removed and the remaining addition was moved
   to a new module.
2. Both delivery modules compile through `lcompile.py`. The only literal `sorry` is the whole
   proof of the public named core theorem. No axiom, unsafe declaration, opaque declaration,
   extern, implemented_by or hollow definition occurs. Scratch `#print axioms` checks and the
   delivery probe permit only the three standard axioms and the expected `sorryAx`.
3. Read the split conjunct against Stacks 09MS and the boundary derivation in 0B8S
   (https://stacks.math.columbia.edu/tag/09MS and
   https://stacks.math.columbia.edu/tag/0B8S). Checked n=0 (the structure module), e=0
   (the original section lifts when its boundary vanishes), and the zero ideal (all sections
   already lift). Nothing needs an affine nonvanishing open or Noetherian hypothesis for this
   obstruction construction. The only retained hole is a strict conjunct; the other conjunct
   has a real proof. This is reported as a decomposition, never as net proof progress.
   Repeated LeanSearch, Lean Finder, Loogle and grep searches with different queries; Lean Finder returned
   cotangent connecting maps, not this sheaf criterion. LeanSearch was unavailable (HTTP
   Internal Server Error), recorded as unavailable without a mathematical verdict. Local searches found the upstream
   quasi-coherence lemmas, so the corresponding split statement and node were removed.
4. The parent now proves quasi-coherence from existing upstream results, with only the
   obstruction/lifting portion left to the sourced core. Proof-only imports are private;
   `tensorPowSection` requires the retained public ClearDenominators import. All old direct
   proof dependencies removed from the parent are accounted for above and retained in the
   core. The unit `sk-thm-curveestimate` realizes `thm-sc-proper-cohomology`, with no realized
   step attached to this item: no unit route is bypassed or changed.
5. The parent node now records its actual conjunction assembly and quasi-coherence proof;
   the new core node records the remaining boundary/graded-algebra/exactness argument.
   `proof_deps` is the union of the step uses in each record. The new node has source,
   complete statement, searches, creation, blueprint, chapter, unit and verbatim Lean record.

Changed: proved quasi-coherence directly; removed its redundant theorem and node; moved the
remaining strict conjunct into its own module; repaired its proof documentation and node;
updated the parent's DAG route, import accounting and progress report.
