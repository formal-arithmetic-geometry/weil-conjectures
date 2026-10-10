# lem-sc-invertible-tensor-qcoherent

## Files written

- `dag/nodes/sec-curve-estimates/lem-sc-invertible-tensor-qcoherent.json`: split the existing statement; 0 new nodes and 0 Mathlib leaves.
- `citations.json`: verbatim statement excerpts for every proof citation.

## Attachments

None. `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorObj` in `WeilConjectures/AlgebraicGeometry/Modules/ProjectionFormula.lean:156` is sorry-free in the 71d63dcf map, but its statement concerns one invertible factor; it does not state the item's conclusion for all integer powers. `IsInvertible.tensorPow` there treats natural powers only. Thus neither is an exact attachment for this item.

## WANTED

The generated `literature/stacks-project/coherent.tex` and `modules.tex` and the imported blueprint files are absent from this read-only clone. I read the public Stacks pages for Tags 09MR, 01CE and 01LA and the corresponding DAG nodes, without writing or downloading source files.

## Issues found

The item had no proof. Its prior Mathlib search correctly found no Mathlib theorem for the sheaf tensor product, but the source Lean checkout has a general theorem for an invertible tensor factor; that theorem alone does not handle integer powers. The existing DAG node `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections` supplies the stronger general quasi-coherent tensor fact, and `lem-pc-tensor-dual-invertible` supplies dual and tensor closure. No statement was changed. The blueprint `from.place` already specified the 09MR affine paragraph, and whole-blueprint searches found no equivalent blueprint statement, so `same_as` remains empty.

## Review by H1

I read Stacks 09MR's affine-open paragraph: the positive-degree vanishing there presupposes that each twisted module is quasi-coherent. I read 01CE item (3) and 01LA item (8), which state the tensor permanence fact used by Step 2. I opened the complete statements of both cited theorem nodes and the invertible-module definition, and checked the item's scheme, quasi-coherent module, invertible module and integer exponent hypotheses against them. No new node was made, so the new-node checks B1-B10 are vacuous. I checked DAG and blueprint searches for tensor and invertibility facts and the Lean source for a finished exact declaration.

Step 1 uses the definition's locally-free-rank-one characterization for the unit and the statement of `lem-pc-tensor-dual-invertible` for the dual and tensor product of invertible modules. These are exactly the two clauses quoted in `citations.json`. The induction itself is elementary: start at the unit, tensor once per successor, and for a negative exponent use a natural power of the invertible dual. This checks the sign and the base case explicitly. Step 2 uses the definition's assertion that invertible modules are quasi-coherent and the quasi-coherence clause, not the affine-sections clause, of `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`. Its statement has the same scheme and two quasi-coherent-module hypotheses, with no finiteness or separation condition. Both external statement nodes are declared as generic tool uses; neither replaces a step of the curve-estimate unit's route.

I tested the small cases $n=0$, where the twist is $\mathcal O_Y$ and the conclusion reduces to the given quasi-coherence of $\mathcal F$; $n=1$, where 01CE applies directly; and $n=-1$, where the dual is invertible by the cited node. On a point scheme these are the ordinary module tensor products; on the empty scheme the assertion is vacuous. I corrected the missing proof and checked that the cited nodes state the facts taken from them. No source statement or hypothesis was weakened.

## Unfinished

Nothing in this one-level split. The two cited theorem nodes have their own work status in the DAG.
