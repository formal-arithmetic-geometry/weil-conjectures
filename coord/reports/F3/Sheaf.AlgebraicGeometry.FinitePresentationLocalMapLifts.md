## What changed

Replaced the sorry in `AlgebraicGeometry.exists_finitePresentation_local_map_lifts`
by a compiling finite-cover assembly proof. It chooses the finite affine subcover
at j, applies single-chart eventual lifting, takes a directed common upper bound,
pulls back the cover, proves finiteness and affineness, supplies the explicitly
canonical composition comparison, and assembles the component maps and equations.
The existing theorem statement and public imports are unchanged.

Added `Sheaf.AlgebraicGeometry.FinitePresentationOneChartMapLift` with one theorem
for eventual lifting on a single specified affine chart. This theorem takes any
supplied cover, assumes only that the selected chart is affine, and asserts one
chart map at all sufficiently late stages. It asserts neither the existence of a
finite cover nor simultaneous lifting on its charts. Updated both DAG proof plans.
Both modules compiled individually through lcompile.py, and the pair compiled in
import order. The new statement was checked on empty charts, zero modules, zero
rings and a singleton directed system; none requires an additional hypothesis.
The empty-cover case of the main proof works because j is inserted into the finite
set whose upper bound is chosen.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_finitePresentation_local_map_lifts`
(node `lem-pc-fp-local-map-lifts`). Added one remaining hole:
`AlgebraicGeometry.finitePresentation_one_chart_map_lift_eventually`
(node `lem-pc-fp-one-chart-map-lift`). Its entire proof is `by sorry` in its new
module, with source and a full proof in words. This is a decomposition, with net
hole count zero, not a complete axiom-free proof of the affine lifting argument.
The finite-cover and common-stage assembly is fully proved without additional holes.

## No longer needed

Moved the direct proof import `Sheaf.Algebra.FinitePresentationColimit` from the
item into the new single-chart module, where affine module descent is needed by
the remaining proof plan.
The existing node `lem-pc-fp-module-map-descent-affine` remains needed below that
node; its module is not globally pruned by this delivery. No further nodes or
modules are claimed pruned. No public imports were removed.

## Where the brief, the DAG or earlier work was wrong

The previous split repeated the full target and was rightly rejected. This split
isolates one supplied affine chart and leaves the finite-cover/common-stage
argument in the original module. The stronger global module-map descent theorem
would cause an import cycle and is not used. The original DAG compressed affine
identifications and finite-cover assembly into one step; they are now separate.
No unit statement or unit route changes. The local checkout does not contain the
Stacks .tex files, so Tags 01ZR and 05N7 were read at the official Stacks pages:
https://stacks.math.columbia.edu/tag/01ZR and
https://stacks.math.columbia.edu/tag/05N7. LeanSearch was unavailable; its failure
is recorded as unavailable, alongside actual LeanFinder and grep searches.

## New nodes

`lem-pc-fp-one-chart-map-lift`: eventual lifting on one specified affine chart,
in `Sheaf.AlgebraicGeometry.FinitePresentationOneChartMapLift`. It inherits the
chapter and unit of the parent and retains the affine finite-presentation colimit
node as its proof dependency. There are no interface change records: every
existing signature and public import is preserved.

## Second reading by F3

1. I compared the delivered item module against the repository version. The target theorem signature is byte for byte unchanged; the proof-only changes add the one-chart import and proof-support imports, and the new module is separately declared.
2. I compiled both modules with `lcompile.py`; they compile without errors or warnings. The only remaining `sorry` is the named one-chart theorem, and it has a docstring, matching DAG node, and no sorry in any definition. No forbidden declarations or extra axioms were introduced; the open theorem is the only source of `sorryAx`.
3. The split-off one-chart statement is strictly smaller than the original finite-cover lifting statement: it fixes one supplied affine chart and asserts persistence, without finite-cover selection, common-stage assembly, or overlap equations. It is true in the stated edge cases and is not duplicated in the library.
4. The proof follows the unit route: the original theorem still performs finite affine-cover selection, common upper-bound construction, affine pullback, and component assembly, while the split theorem isolates only the affine descent step. The affine finite-presentation colimit dependency remains in the new module; no unnecessary proof import was made public.
5. The DAG nodes and Lean declarations agree on names, statements, proof dependencies, source, unit, and proof origin. The new node records the split theorem and the original node records the assembly proof. I changed only the report after this review; no mathematical or interface changes were needed.
