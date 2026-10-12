## What changed

Proved `AlgebraicGeometry.pic_boundary_base_change_transport` with its original signature.
Added `Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange`, containing the strictly
smaller geometric boundary bijection and point-class pullback statement. The main proof
proves degree preservation directly from module degree base change, obtains injectivity
from the existing `picZero_torsion_base_change` at n=1, maps the generator sets and closures,
and constructs the equivalence with `Subgroup.equivMapOfInjective` and `subgroupCongr`.

## Proved and sorry left

Closed: `AlgebraicGeometry.pic_boundary_base_change_transport` (1 original hole).
Added: `AlgebraicGeometry.boundary_point_class_base_change`
(`lem-sc-boundary-point-class-base-change`, 1 hole). No holes remain in the original module.
This is a decomposition with net zero holes, not a full geometric proof.
The new lemma asserts only boundary point/class transport; it has no degree-zero subgroup,
subgroup closure, injectivity, or equivalence conclusion. Empty and singleton boundaries
satisfy it; the original chosen P0 excludes the empty case in the combination proof.

## No longer needed

Removed direct imports: `Sheaf.AlgebraicGeometry.BaseChangeCurve`,
`Sheaf.AlgebraicGeometry.GenusInvariant`,
`WeilConjectures.AlgebraicGeometry.EffectiveCartier`,
`Mathlib.AlgebraicGeometry.AlgClosed.Basic`, and
`WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`.
Retained `WeilConjectures.AlgebraicGeometry.Picard.Degree` for degree invariance.
Replaced the direct `lem-sc-genus-invariant` proof dependency with the existing
`lem-sc-piczero-torsion-base-change`, using only its injectivity clause.
The geometric dependencies `lem-sc-base-change-curve`,
`lem-weil-pbc-closed-point-residue-field-base`,
`lemma-nagata-compactification-base-change`, and
`lem-pc-divisor-line-bundle-properties` move to the new boundary comparison node;
they are not claimed globally unnecessary. No blueprint unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The available existing Picard-zero torsion comparison
already contains the injectivity needed here, and the source degree-base-change theorem
already proves degree invariance. The original plan's Jacobian argument need not be repeated.
The source copy of `PicZeroJacobianPointComparison` was not yet present in the local compiled
library, so the proof uses the available higher comparison interface instead.

## New nodes

`lem-sc-boundary-point-class-base-change` records steps 1 and the point-class portion of
step 2, with a complete natural-language proof and the original geometric dependencies.
Its module is `Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange`.
Searches: LeanFinder gave elliptic-curve injectivity results; Loogle supplied the abstract
map-closure lemma; grep found no point-class base-change theorem. The original target node's
proof and proof_deps now follow the compiled proof.

## Earlier second reading (a previous round; superseded)

The new boundary theorem has the same field-extension, compactification, and relative-dimension hypotheses as its source step, and concludes exactly a boundary-point bijection with point-class pullback. The target proof uses it only for Q0 and generator transport; degree preservation and injectivity come from existing declarations. The subgroup closure argument preserves the unit route and compiles with the two delivered modules.


## Second reading by V3

1. I compared the delivered target module and its existing DAG node with the repository. The target theorem signature is unchanged byte for byte; the node update changes only `proof`, `proof_deps`, and `proof_origin`, as allowed.
2. I compiled both delivered modules with `lcompile.py --all`; they compile without errors. The target declaration has no `sorry`; the new geometric comparison theorem is the single named split-off hole and has a matching node and source proof description. The axiom probe reports only `sorryAx` from that intentional open theorem, together with the permitted standard axioms.
3. I checked the new statement on empty and singleton boundaries and verified that it is strictly smaller than the target: it asserts only a boundary-point equivalence and point-class pullback, with no degree-zero subgroup, injectivity, closure, or subgroup equivalence conclusion. Searches found no existing theorem with this statement. I clarified its docstring and DAG proof step with the finite closed-complement argument.
4. I checked the proof route against the code. It uses the new boundary comparison, degree invariance, and the existing Picard-zero injectivity theorem, then explicit subgroup closure algebra. The retained imports are used; the report's removed imports are not needed. The unit route remains the boundary compatibility step followed by degree and subgroup transport.
5. I checked the DAG agreement: the new node records the exact Lean declaration, source, dependencies, searches, and `status: split`; the target node's owned proof fields follow the compiled proof. No statement or definition was changed.

I changed only the new theorem's proof/docstring metadata and corrected the existing node's stage-3 owned fields; no further holes were closed and no new hole beyond the named geometric comparison was added.
