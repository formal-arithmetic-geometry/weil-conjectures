## What changed

Completed the earlier sandbox candidate for
`Sheaf.AlgebraicGeometry.HomLocalKernelOfPresentation`.
`AlgebraicGeometry.Scheme.Modules.homObj_locally_kernel_of_local_presentation`
now has a complete proof, with its existing signature and visibility unchanged.
The proof takes the opposite of the cokernel cofork, applies the contravariant
internal Hom functor, identifies the finite biproducts by additivity and
`homObjUnitIso`, and transports through `overEquiv V` to scheme restriction.
The specified presentation, open, and ranks are retained exactly.

Added proof-only imports of
`Mathlib.Algebra.Category.Grp.FilteredColimits`,
`Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels`, and
`Mathlib.CategoryTheory.Monoidal.Closed.Braided`.
The filtered-colimit import supplies the small-site sheafification instances
previously inherited from the removed proof dependency.
Retained all three public imports and the proof-only `InternalHomFree` import.
Updated the theorem's proof explanation and the existing node's proof,
proof dependencies, and proof origin to describe the categorical route.

The earlier attempt timed out while the elaborator unfolded slice-site structures.
Local transparency options and a typed alias for the restricted unit avoid that
unfolding. No library definition, interface, or compiler time limit was changed.

## Proved and sorry left

Closed the sole existing hole:
`AlgebraicGeometry.Scheme.Modules.homObj_locally_kernel_of_local_presentation`
(node `lem-weil-pbc-coherent-hom-local-kernel-from-presentation`).
One of one sorries proved; zero new holes and zero split-off statements.
No `sorry` remains in the delivered module. No new modules or declarations were added.
The axiom probe is run by the delivery dry check.

## No longer needed

Removed the proof-only import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.HomFinitePresentationKernel` and the proof
edge to `lem-weil-pbc-sheaf-hom-finite-presentation-kernel`.
Neither `SheafOfModules.homObj_precomposition_exact` nor
`SheafOfModules.homObj_finitePresentation_kernel` is used by this proof.
Their right-exact sequence and coordinate formulas are unnecessary here:
the cokernel universal property supplies the limiting kernel fork directly.
This is pruning of this item's dependency edge; other items may still need that module.
No unit statement or realized unit step is bypassed: the item and its removed
auxiliary dependency are below the unit's realized route.

## Where the brief, the DAG or earlier work was wrong

The DAG's finite-free reindexing and exact-sequence route is valid but longer
than necessary. Upstream's additive contravariant internal Hom already sends
finite biproducts of units to finite biproducts of the target, and Mathlib sends
opposite cokernel coforks to limiting kernel forks. These proved declarations
close the result directly without the presentation-kernel lemma.

Checked the cited Stacks statements at tags 01CO, 01CQ, 01CP, and 0E8H using the
Stacks website because this clone contains only the literature lists.
The given presentation implies exactly the same finite-sum kernel statement
on the same open; neither G nor F needs coherence. Empty sums (m or n zero)
and the empty open use the same universal properties without exclusions.
No statement is disputed and no forced adaptation is required.

## Second reading by E1

1. Interface: PASS. Compared the sole delivered module with the repository using
   `diff` and checked the complete theorem signature byte for byte. It is identical;
   there are no added declarations or definition changes. Existing public imports
   and the local biproduct instance are unchanged. The two transparency options
   apply only to this theorem.
2. Proof and axioms: PASS. Independently compiled the delivered file with
   `lcompile.py`, without errors or warnings (53.9 seconds). A scratch copy with
   `#print axioms AlgebraicGeometry.Scheme.Modules.homObj_locally_kernel_of_local_presentation`
   compiled (52.6 seconds) and reported exactly `propext`, `Classical.choice`,
   and `Quot.sound`, with no `sorryAx`. The delivered source contains no `sorry`,
   forbidden declaration, or hollow definition. The cokernel, kernels, biproducts,
   and comparison isomorphisms are universal constructions, not arbitrary data
   selected from an unproved existence theorem.
3. Split statements: PASS, vacuous. No statements were split off and no holes added.
   Read the upstream unit-Hom, additivity, restriction-Hom, and monoidal-closed
   declarations used by the proof, and Mathlib's opposite-cokernel construction.
   Empty ranks and the empty open introduce no extra hypothesis or exceptional case.
4. Route and pruning: PASS. Searched the existing Lean library for Hom/cokernel
   kernel results and read the former dependency's exact-sequence route. The direct
   limiting-fork route avoids the extra exact-sequence and coordinate constructions.
   Each new proof-only import supplies used machinery: sheafification instances,
   opposite cokernel forks, or contravariant internal-Hom limit preservation.
   InternalHomFree supplies additivity, homObjUnitIso, and restriction comparisons.
   The complete removed old proof edge and import appear under No longer needed.
   Read `dag/units/sk-thm-p1.json`: neither this auxiliary node nor its removed
   dependency occurs in `realized`; every unit statement and realized step is kept.
5. Nodes: PASS. The only changed node fields are `proof`, `proof_deps`, and
   `proof_origin`. Its three steps match the actual limit-preservation proof,
   biproduct conjugation, and transport through overEquiv. The proof dependencies
   are exactly the union of the steps' uses; the statement and Lean record are
   unchanged. There are no new nodes or change records to audit.

Second reading changed only this report, adding the independent checks and verdicts.
No repair to the Lean proof or DAG was needed. One existing hole closed, zero holes
added; this is a proof, not a decomposition.
