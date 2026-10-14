## What changed

Proved `AlgebraicGeometry.Scheme.Modules.tensorGradedCoefficient_action_support`
with its statement unchanged. Added proof-only imports of
`Sheaf.AlgebraicGeometry.TensorKernelSectionProduct` and
`Sheaf.AlgebraicGeometry.ClosedImmersionUnitEpi`.
The explicit factorization is the action composed with `(T.degree (n+d)).tau_1`.
Local lifts and the presentation identities verify the equality.

Added the fully proved public theorem `tensorKernel_section_product` in its own module.
It explicitly constructs the kernel-valued tensor product using the already proved
`boundaryIdealKernelIso_exists` API and the monoidal calculation `ideal_tensor_shuffle`.
The item's private `unit_local_lift` and `homogeneous_action_support` are fully proved.
Updated the item's DAG proof to match this route.

## Proved and sorry left

Closed the one hole in the module assigned by the brief: `AlgebraicGeometry.Scheme.Modules.tensorGradedCoefficient_action_support`
(node `lem-sc-tensor-coefficient-action-support`). Added no holes.
`AlgebraicGeometry.Scheme.Modules.tensorKernel_section_product`
(node `lem-sc-tensor-kernel-section-product`) and all private helpers are proved.
Neither delivered module contains `sorry`. This is a proof, not a decomposition.
Against the fetched baseline, which removed the assigned module during this session,
the assigned theorem is a new proved declaration, not a net existing-hole closure.

## No longer needed

No original import was removed, and no module is claimed globally pruned.
The public import `SquareZeroTensorGradedProductProjection` remains necessary for
`tensorGradedSection` in the statement. Its product/projection theorems,
`SquareZeroTensorGradedQuotientMultiply`, `SquareZeroTensorSectionProductComparison`,
`square_zero_ideal_tensor_unit_isIso`, and an independence-of-lifts/gluing argument
are not used by this proof. They remain reachable through the retained public imports.

`hD` and `hrestrict` remain in the unchanged statement; arbitrary comparison data
suffice, and naturality of the given global endomorphism handles restrictions.
The fields `squareZero`, `k_colimit`, `k_orthogonal` and the quotient projections are unused.
The original direct proof dependency `lem-weil-pbc-closed-immersion-unit-quotient` is
replaced by its epi interface for lifting, but it remains a transitive dependency of
the ideal-kernel comparison and is not globally pruned.

Removed unnecessary trial imports of
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`,
`Mathlib.Topology.Sheaves.LocallySurjective`, `Mathlib.CategoryTheory.Sites.Abelian`,
`Mathlib.Algebra.Category.Grp.Abelian`, `Mathlib.Algebra.Category.Grp.EpiMono`, and
`Mathlib.CategoryTheory.Monoidal.CoherenceLemmas`; the retained imports already
export the required APIs.

## Where the brief, the DAG or earlier work was wrong

The original plan's independence of lifts and gluing are unnecessary for a support-only
assertion. A degree projection supplies the factorization, and local image membership
proves its equality by separation. No realized unit statement or step is bypassed.
No signature, definition, visibility, or module held by another group was changed.

Local literature files are absent in this clone. The source was checked at
[Stacks 09MS](https://stacks.math.columbia.edu/tag/09MS), `coherent-equation-ses`
and its graded sum, and [Stacks 08KS](https://stacks.math.columbia.edu/tag/08KS),
the closed-immersion module comparison. The new theorem is the ideal-tensor calculation
for this sequence; its construction needs no Noetherian or square-zero hypothesis.
The proof covers zero degrees and empty opens uniformly via associators and unitors.

## New nodes

`lem-sc-tensor-kernel-section-product` records the proved multiplication lemma in
`lean/Sheaf/AlgebraicGeometry/TensorKernelSectionProduct.lean`.
Whole-blueprint search for "tensor kernel" found no matching node; Lean Finder,
Loogle, LeanSearch (unavailable), and grep searches are recorded in the new node.
The dry run fetched a baseline on which the assigned module and its original node
are absent, although they were present at the beginning of this session. Thus
`lem-sc-tensor-coefficient-action-support` is also reintroduced, with the original
statement unchanged and its new proof. Its new-node ownership records P3 for this
reintroduction. The prior M3 original-node snapshot is kept only in the sandbox scratchpad.

`coord/changes/tensor-coefficient-action-support-reintroduction.md` records the
reintroduction against that fetched base. No consumer adaptation is necessary:
`tools/downstream.py` reports the module unknown at that base, and the current
`TensorGradedCoefficientSheafAction` no longer imports it. The reviewer should assess
this baseline discrepancy before landing. All proof-only imports remain private.

## Second reading by P3

1. Interface: compared both delivered module paths with the current repository using
   diff. Both are absent on this baseline, as the change record declares. Compared
   the assigned theorem's complete signature byte for byte with the original M3 node
   snapshot in scratchpad/original-node.json: identical. No existing declaration,
   definition, target, or consumer is edited. The baseline discrepancy is confirmed:
   this delivery restores a proved theorem, but closes no existing baseline hole.
2. Proof: compiled both modules in import order with lcompile.py, without errors or
   warnings. A scratch copy with #print axioms reports exactly propext,
   Classical.choice and Quot.sound for both public theorems, with no sorryAx.
   No delivered module contains sorry or a prohibited declaration. Read the three
   private proofs as well. The only chosen comparison used to construct data is the
   existing ideal-kernel isomorphism, uniquely determined by its inclusion equation;
   the action factorization is explicitly r followed by the degree projection.
3. Intermediate statements: no statements are split off with sorry. The proved
   tensorKernel_section_product is strictly the local tensor-kernel calculation;
   it has neither the graded presentation nor action hypotheses of the assigned
   theorem. Checked zero degrees, identity and empty closed immersions, and empty
   opens: the ideal-kernel comparison and monoidal unitors cover them uniformly.
   Repeated Lean Finder, Loogle and Mathlib grep searches using restriction kernels,
   locally free sheaves and kernel.lift; searched Sheaf and upstream module sources
   for kernel/tmulSection formulas. Found no duplicate or shorter ready-made result.
   kernel.lift alone still needs the tensor-unit vanishing calculation supplied here.
4. Route and pruning: checked the explicit factorization, local lift, image equality,
   projection identity and sheaf separation from the conclusion downward. No gluing
   or independence-of-lifts lemma is necessary. The statement uses tensorGradedSection,
   so its public import stays; the other imports are proof-only. The helper's public
   import supplies tensorGradedUnit in its signature. All direct imports are used.
   Of the original node's three proof_deps, the presentation remains direct, the
   unit-quotient theorem is replaced by its epi interface, and the ideal-tensor-unit
   node moves to the proved helper's dependencies. Both replaced direct dependencies
   remain transitive; no module is claimed pruned. sk-thm-curveestimate.realized names
   thm-sc-proper-cohomology, not this node or helper; its route is unchanged.
5. Metadata: checked both node signatures against the Lean and checked proof_deps
   equals the union of proof-step uses. Read proof and proof_origin against the code;
   checked the new-node source, search, ownership, blueprint, chapter, unit and Lean
   records. The restored node's mathematical statement matches its original snapshot.
   The reintroduction change record and the report disclose the absent baseline and
   lack of current consumers. Verdict: true proved declarations, no decomposition,
   no claimed net closure gain on the current baseline, and no interface weakening.

Changes made by the second reader: replaced the assigned theorem's stale docstring
about independence of lifts and gluing with the actual projection-and-separation
proof; corrected the change record's count from three private helpers in the assigned
module to two. No proof term, signature, definition, import or node needed repair.
