## What changed

Proved `WeilConjectures.NormalizedIntegralPurityTrace.quotientProjection` without
changing its statement. A proved private `quotientTower` gives the direct quotient
maps, with identity and composition laws supplied by Mathlib's ideal quotient API.
The proved private `coefficientTower_map` identifies these maps with the transition
maps of the actual inverse sequence of coefficient sheaves. Applying `limit.w`
after forgetting commutativity proves the required projection equation, including
the identity quotient. The arbitrary scheme and coefficient field are retained.

The retained draft failed to infer the ideal inclusions in the composition proof;
these are now explicit. Profiling located the slow elaboration in the comparison
of successive transition maps. Explicitly unfolding just those maps, rather than
asking `rfl` to discover their common presentation, fixes that comparison. Local
irreducibility of `Padic.coefficientExtensionIdeal` prevents unnecessary unfolding
of the valuation construction. Temporary diagnostics were removed.

Only the item module and this report are delivered. No existing public signature,
definition, visibility, import, target, or DAG dependency was changed. The proof
implements the projection argument already recorded in its docstring, so the
existing node's route is retained. Server compilation and the delivery preflight
check the complete final file.

## Proved and sorry left

Closed one of the item's two original holes:
`WeilConjectures.NormalizedIntegralPurityTrace.quotientProjection`.

One original hole remains unchanged:
`WeilConjectures.NormalizedIntegralPurityTrace.normalizedIntegralPurityTrace`
(node `lem-sf-normalized-integral-purity-trace`).

Zero holes were added, zero statements were split off, and there is no `sorry`
in a definition or private helper. This is a partial proof delivery, with a net
reduction of one textual hole in the item.

For the next worker: `integral_residue_tor` provides the residue interval clause
and integral finite-Tor membership. Unfold `FiniteReductions` before evaluating
`A.finiteReductions`; it supplies the forward purity square and the two reduction
isomorphisms. Cancellation with inverses then gives the inverse square.
`PurCompactSupport.reductionComparison_isIso` supplies support invertibility after
the two reduction bridges and `finiteImageIso`. The remaining substantial glue
identifies the actual exceptional counit and source/target/support quotient
normalizations. The finite equations use `finiteReductionOfPurity`,
`finiteReductionOfSmoothTrace`, and the normalization property of
`existsUnique_finiteReductionExceptionalComparison`.

## No longer needed

No existing imports, nodes, or modules were pruned. The main theorem remains open,
so none of its declared proof dependencies is withdrawn. The quotient projection
proof uses Mathlib's `Ideal.Quotient.factor_eq`, `factor_comp_apply`, and `limit.w`,
with no additional proof import or new public dependency.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped because the compile server could not create a
temporary directory on a full device. That infrastructure failure is resolved in
this session. The retained draft additionally needed explicit ideal inclusions
and a controlled transition-map comparison, as described above. No mathematical
statement error or change to the blueprint unit route was found.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
