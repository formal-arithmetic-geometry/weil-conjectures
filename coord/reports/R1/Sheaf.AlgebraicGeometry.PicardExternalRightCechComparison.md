## What changed

The target signature and docstring are unchanged. Its proof now chooses the three
normalized scalar-model cup maps, obtains a natural transformation of the fixed
right Cech functors, compares each quasi-coherent coefficient, and forms the
short-complex morphism with `S.mapNatTrans`. Tensor-cycle uniqueness identifies
its transported homology components with the chosen cup maps; isomorphism
cancellation proves the three displayed equations.

Added `PicardRightCechCupConstruction`, `PicardRightCechCupHomology`, and
`PicardExternalCupHomologyUnique`. The first separates the actual natural
cochain construction, pinned by an explicit Alexander--Whitney tuple formula;
the second separates the geometric affine Cech-to-scalar-model comparison.
The third proves the algebraic uniqueness step using the existing tensor
Kunneth theorem, surjective factor homology projections, tensor extensionality,
and direct-sum extensionality. Definitions contain real formulas, no holes.
The section pullback uses the existing adjunction theorem whose conclusion
pins every unit component to a specified formula.

All five sandbox modules compile in import order with `lcompile.py --all`.
Each file completes in under 11 seconds. The models module is byte-for-byte
identical to the repository version and is not a delivered adaptation.
The target module also compiles individually against the sandbox closure.

Sources checked: [Stacks 0BED](https://stacks.math.columbia.edu/tag/0BED),
[07MB](https://stacks.math.columbia.edu/tag/07MB), and
[0FKV](https://stacks.math.columbia.edu/tag/0FKV). The local literature checkout
contains lists only; the official tag pages supply the cited construction and
comparison arguments. Finite affine covers retain the original geometric route;
no unit statement or unit step is bypassed.

## Proved and sorry left

Closed in the compiled delivery:
`AlgebraicGeometry.Scheme.Modules.picardExternal_right_cech_comparison`
(node `lem-sc-picard-external-right-cech-comparison`). This is a decomposition,
not a net hole reduction: one original hole is closed and two strictly
separate geometric holes are added below it (net -1 before closure accounting).

Proved and compiled:
`AlgebraicGeometry.Scheme.Modules.picardExternalCupHomology_unique`
(node `lem-sc-picard-external-cup-homology-unique`). It has no local sorry.
The proof uses the existing `HomologicalComplex.tensor_kunneth_nat`; the
standard project convention treats its existing proof dependencies as next items.

Added holes, exactly two:

- `AlgebraicGeometry.Scheme.Modules.picardRightCechCup_exists`
  (`lem-sc-picard-right-cech-cup-construction`): natural cochain construction
  with explicit front/back section coordinates. It makes no homology assertion.
- `AlgebraicGeometry.Scheme.Modules.picardRightCechCup_homology`
  (`lem-sc-picard-right-cech-cup-homology`): affine comparison and normalization
  of the transported homology map. It assumes the specified cochain construction
  and neither constructs it nor packages any coefficient sequence or d maps.

Both have complete proof descriptions and matching nodes. The item itself has
no remaining sorry in the draft. No existing statement is weakened, no other
existing module is adapted, and no hole is placed in a definition.

Edge cases checked in the formulations: arbitrary covers are allowed in the
cochain construction; empty finite affine covers in the comparison force empty
schemes; zero modules give zero pairings; in degree zero the Kunneth sum has
only the (0,0) index. Repeated indices use the standard shared front/back vertex.

## No longer needed

None of the original public imports is removed. No geometric node or module is
claimed pruned from the target closure. The target's direct proof dependencies
are replaced by the two geometric helper nodes and the proved uniqueness node,
but the original geometric dependencies are retained in the homology helper's
proof plan. The original direct dependencies no longer applied by the target
itself are:

- `lem-sc-cech-comparison-map-iso-affine`
- `lem-sc-cech-comparison-map-naturality`
- `lem-sc-cech-comparison-natural`
- `lem-sc-picard-affine-diagonal-intersections`
- `lem-sc-picard-cech-cup-pullback-compat`
- `lem-sc-picard-kunneth-resolution-model`
- `lem-sc-qcoh-cech-total-tensor-nat-iso`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `lem-weil-pbc-module-pullback-quasi-coherent`
- `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`

These are moved under the geometric comparison plan, not removed from the route. The construction statements need `TensorPullbackAdjunction` rather
than publicly exposing `CechRefinementCochainMap`; they use `CechCupProduct` for
the existing front/back faces. No unrelated Kunneth invertibility or exactness
module is imported.

## Where the brief, the DAG or earlier work was wrong

The supplied plan's geometric lemmas operate on module-valued Cech complexes or
additive underlying complexes; they do not directly state the scalar-valued,
zero-extended functor transformation and homology transport used by this target.
The two helpers isolate those actual interface steps rather than restating the
whole coefficient-sequence result. The existing left-variable comparison cannot
be applied to these fixed right-variable covers without additional comparisons.

Earlier compilation was blocked by an unavailable models artifact. This is no
longer a blocker: the unchanged sandbox models module compiles, as do all
delivery modules. No repository source or shared compiled artifact was changed.

## New nodes

`lem-sc-picard-right-cech-cup-construction`, in
`dag/nodes/sec-abelian-varieties/`, matches the explicit tuple-coordinate
predicate, its section/face helpers, and natural-transformation existence in
`PicardRightCechCupConstruction`.

`lem-sc-picard-right-cech-cup-homology`, in the same directory, matches the affine
homology comparison of a transformation satisfying that predicate. The predicate
specifies an actual cochain map; no unconstrained natural transformation is
assumed to induce external cup.

`lem-sc-picard-external-cup-homology-unique`, in the same directory, matches the
homology normalization predicate and its proved uniqueness theorem. It supplies
the real algebraic step between geometric compatibility and the target's
conjugation equations. No change records or forced adaptations are required.

## Second reading by R1

1. PASS: diffed the target and the staged models module against the repository.
   The target declaration signature and docstring are byte-for-byte unchanged;
   its only changes are a plain proof import and the proof body. The models copy
   is identical. There are no forced adaptations, definition changes to existing
   declarations, or change records.
2. PASS: compiled the five sandbox modules in import order and the target alone.
   Scanned every delivered source: exactly the two listed named theorem holes,
   no hole in any definition and no forbidden declaration or implementation
   facility. A scratch `#print axioms` for the target, uniqueness theorem, and
   both split theorems reports only propext, Classical.choice, Quot.sound and
   sorryAx from the remaining local and imported holes. The uniqueness theorem
   has no local hole; its inherited sorryAx is not claimed discharged.
3. PASS: read both split statements and their complete docstring proofs. The
   construction specifies front/back coordinates and naturality for arbitrary
   families, whereas homology transport assumes that construction and supplies
   affine comparisons for one coefficient. Neither restates the sequence target.
   Checked p=q=0 (both faces use the common vertex), zero coefficients, repeated
   tuple entries and empty families; an empty covering family in the comparison
   forces an empty scheme. The pullback section definition uses a pinned unit
   component, not an arbitrary existence witness: the adjunction theorem fixes
   every unit section by its displayed formula. New leanfinder, loogle and grep
   searches found no matching scalar external construction/transport theorem.
   Read existing Cech cup, refinement and coefficient-naturality declarations;
   they are ingredients, not the stated scalar functor transformation. The
   uniqueness proof uses existing tensor Kunneth and Mathlib extensionality.
4. PASS: reviewed the top-down assembly, its isomorphism cancellation, and
   `S.mapNatTrans`. No shorter ready theorem for these fixed right covers was
   found. Imports serve public statements/definitions except the two plain proof
   imports (homology helper in the target, tensor Kunneth in uniqueness). No
   module is pruned. The cube unit's realized arrays are unchanged (currently
   empty); this below-unit refinement preserves the finite affine Cech route.
5. PASS: checked all four node statements against their Lean signatures,
   declaration lists, sources, proof steps and dependency unions. The original
   node now records the actual construction/transport/uniqueness assembly. The
   new nodes carry the required creation and blueprint records. All original
   geometric dependencies remain in the homology helper's proof plan.

Changes made by this reading: corrected stale compilation-blocker claims and
reported the one-closed/two-added decomposition explicitly; restored the original
node's immutable mathlib_searches field; completed the direct-dependency pruning
accounting below. No Lean proof or statement needed repair. Neither geometric
hole can be closed in a few minutes with the available scalar interfaces.
