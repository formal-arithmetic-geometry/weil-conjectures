## What changed

Replaced the sorry of `AlgebraicGeometry.exists_selfTor_ordinary_resolution_sections`
by a complete Lean proof from chosen-lift geometric compatibility and the already-proved
`ModuleCat.quotient_tensor_resolution_lift_homotopy`. The proof identifies the quotient
homomorphisms by quotient surjectivity, obtains a tensor-chain homotopy between the
chosen and arbitrary supplied lifts, and rewrites using equality of their homology maps.
The original declaration's type, universes, visibility and docstring are unchanged.

Added `Sheaf.AlgebraicGeometry.SelfTorOrdinaryLocalizedComparisons`, containing the
strictly smaller geometric construction: affine coordinates compatible with ONE chosen
augmented comparison for each inclusion. It does not assert compatibility with every
lift. Its docstring and node spell out the augmented tensor zigzag and its geometric
naturality. The real combination proof supplies the missing arbitrary-lift independence.
No definition chooses data from an unproved existence theorem; no definitions were added.
No target, shared interface, or other group's module was changed.

The unit record `sk-thm-picard-duality` has no realized statement or steps at this node;
this refinement stays below the unit level and retains the original geometric route.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_selfTor_ordinary_resolution_sections`
(node `new-b3-self-tor-ordinary-resolution-sections`).

Added and still sorry: `AlgebraicGeometry.exists_selfTor_ordinary_localized_comparisons`
(node `new-h3-self-tor-ordinary-localized-comparisons`). Its proof is exactly `by sorry`.
There are no sorries left in the assigned module and no other added holes.
This is one decomposition (one closed upper hole, one simpler lower hole), with net
hole change zero; it is not a complete proof of the affine geometric computation.
Lift independence now uses an existing fully proved algebraic theorem.

Validation: both modules compiled with lcompile.py, the assigned module in about ten
seconds after setting maxHeartbeats to 800000 (no wall-time limit changed). The proof
uses no nonzero-ring, positive-degree, nonempty-open, localization-flatness or restricted-
projectivity assumptions. The remaining statement was checked on n = 0, I = top and
empty basic opens: its zigzag and algebraic comparison construction still use zero
modules and zero rings without new hypotheses.

## No longer needed

Removed direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`
- `Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`
- `Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction`
- `Sheaf.AlgebraicGeometry.AffineChartTotalTensor`
- `Sheaf.AlgebraicGeometry.OpenKFlatTensorHomologyComparison`

These imports and their original DAG nodes are retained by the new geometric subproblem;
they are moved down, not pruned from the targets' transitive import closure. The tilde
sections and adjunction nodes likewise remain below that subproblem. No node or module
is claimed to be globally pruned. The assigned node now directly depends only on the new
chosen-lift node and `new-h2-quotient-tensor-resolution-lift-homotopy`.
All existing public imports were retained to preserve the importer-visible interface.

## Where the brief, the DAG or earlier work was wrong

The original plan included naturality for every supplied algebraic lift in the geometric
zigzag argument. That part already follows from the proved quotient-tensor lift homotopy
API, without having to arrange geometric naturality separately for every supplied lift.
The new subproblem retains only existence and compatibility with one lift. The harder
geometric construction is still open and explicitly reported as such.

Searches: leanfinder returned flat tensor exactness and projective-resolution APIs;
loogle returned ProjectiveResolution.lift and its homotopy lemmas; LeanSearch was
unavailable with Internal Server Error (recorded in the node); the grep service found
no ordinary comparison. Local rg found the analogous derived comparison, but it imports
this item and would create a cycle. Read the existing algebraic lift-homotopy proof and
all original geometric dependency signatures. The Stacks pages 08DX(2) and 00LS(1),(2)
were read directly; the latter uses projectivity only through lifting across surjections.

## New nodes

`new-h3-self-tor-ordinary-localized-comparisons` records the ordinary geometric affine
coordinate construction and compatibility with one augmented algebraic comparison per
basic inclusion. Its source, complete proof in words, three searches, unchanged statement
dependencies, inherited chapter/unit/blueprint provenance, and verbatim Lean statement
are in its JSON. Its proof dependencies retain the original geometric route and add the
existing quotient-resolution comparison existence theorem. No change record is required:
there are no definition or statement changes and no forced adaptations.

## Second reading by H3

1. The delivered module compiles, and its target declaration has the same signature as the repository version. The proof uses the chosen-lift comparison followed by the quotient-tensor lift homotopy, so the target statement is proved without changing its hypotheses or conclusion. Verdict: unchanged and valid.

2. The split-off declaration is strictly weaker than the target: it supplies one compatible quotient-resolution comparison for each basic inclusion, while the target quantifies over every supplied comparison. Its statement is well-typed and covers the edge cases recorded in the report. Verdict: true and exactly the needed reduction.

3. The new node records the declaration, source, proof plan, dependencies, searches, and blueprint provenance. The remaining `sorry` is named and documented in its docstring; it is not inside a definition. Verdict: DAG and Lean agree.

4. I checked the proof route against the imported algebraic homotopy theorem and found no shorter existing theorem. The removed direct proof imports are used only by the split-off geometric construction; no target-reachable dependency was accidentally deleted. Verdict: pruning record is complete.

5. The unit `sk-thm-picard-duality` has no realized statement or step at this node, so the refinement remains below the unit level and does not bypass the planned route. Verdict: unit route preserved.

Changed during second reading: added this review record only; no Lean declarations or node statements were altered.
