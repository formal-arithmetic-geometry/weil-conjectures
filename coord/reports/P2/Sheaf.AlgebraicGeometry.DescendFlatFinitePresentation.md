## What changed

Replaced the `sorry` in `AlgebraicGeometry.exists_flat_stage_of_limit` by a complete Lean
proof from the existing ring theorem
`RingHom.exists_eventually_flat_of_colimit_flat` and the new affine-chart comparison
`AlgebraicGeometry.exists_flat_descent_affine_charts`. Added its proof-only import.
All existing signatures, public imports, visibility and docstrings are unchanged.

The proof constructs the directed upper-tail preorder, applies ring descent separately
to each chart, and uses `Finset.exists_le` on the finite image of the chosen stages.
The final scheme-flatness assertion follows from the stage comparison. The empty-family
case works because the upper tail contains the initial stage.

Added `Sheaf.AlgebraicGeometry.FlatDescentAffineCharts`, containing a concrete ring-data
structure, three explicitly defined flatness predicates, and the geometric translation
of steps 1–4 and the local gluing part of step 6 of the original plan. Its statement has
no flatness hypothesis and concludes no existence of a flat stage: it produces chart
comparisons valid independently of the algebraic descent theorem. The existential chart
data are eliminated only inside the theorem proof; no definition chooses arbitrary data
from an unproved existence statement.

Updated the target node's proof and dependencies to match this reduction. Both modules
compile with no warnings using `lcompile.py --all`.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.exists_flat_stage_of_limit`
(node `lem-weil-pbc-descend-flat-finite-presentation`). Its proof contains no `sorry`.

Added one hole, the whole proof of the public theorem
`AlgebraicGeometry.exists_flat_descent_affine_charts`
(node `lem-weil-pbc-flat-descent-affine-charts`). Its module and node give the source,
full statement and complete natural-language proof. This is a decomposition, not a net
hole reduction: one original hole closed, one new hole added. The imported existing
`RingHom.exists_eventually_flat_of_colimit_flat` remains a dependency with its existing
hole; it was neither changed nor newly stated in this delivery.

## No longer needed

No imports removed and no modules pruned. The original geometric proof dependencies
now belong to `lem-weil-pbc-flat-descent-affine-charts`: they are still needed by its
proof, rather than by the final ring-descent/common-bound argument. In particular,
`Sheaf.AlgebraicGeometry.LimitAffineTransition` is retained. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original six-step plan is followed. The ring theorem
fits the chart's tensor-product predicates directly, including the proof-irrelevant
inequalities of a directed preorder, so no additional tensor-product transport or
persistence theorem is necessary in the main proof.

The local copy of `literature/stacks-project/limits.tex` is absent. Read Stacks Tag 04AI
at https://stacks.math.columbia.edu/tag/04AI and checked its affine reduction and algebra
step against the node. LeanFinder and Loogle searches ran; LeanSearch returned an
Internal Server Error and is recorded as unavailable, not as evidence of no match.
Blueprint search for 04AI and source searches found no existing chart-package statement.

Mathematical edge cases checked: an empty source allows zero charts, an empty chart
family still has an upper bound in the nonempty upper tail, identity/constant systems
use the same tensor-product comparison, and only a directed preorder (not antisymmetry)
is required. The chart theorem uses no descent assertion; its ring finite-presentation
field follows from local finite presentation on the affine source and target opens.

## New nodes

`lem-weil-pbc-flat-descent-affine-charts` is the geometric affine reduction, with one
public theorem in `lean/Sheaf/AlgebraicGeometry/FlatDescentAffineCharts.lean`. It keeps
original steps 1–4 and the local gluing part of step 6, and does not use the parent
descent theorem or its algebraic eventual-flatness step.

`def-weil-pbc-flat-descent-chart` records the real ring-data structure
`AlgebraicGeometry.FlatDescentChart` and its baseFlat, stageFlat and limitFlat predicates
in that module. Every definition has a concrete body, and none contains `sorry`.

No existing interface was changed, no other module was adapted, and no change record
is necessary.

## Second reading by P2

1. **Interface and accidental changes.** Compared the delivered `DescendFlatFinitePresentation.lean` with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; the only change there is a proof-only import and the proof body. The added chart module introduces the declarations recorded by its new nodes.

2. **Compilation and proof hygiene.** Compiled both delivered modules with `lcompile.py --all`; they compile without errors or warnings. Searched the delivered Lean files: the only `sorry` is the named split theorem `AlgebraicGeometry.exists_flat_descent_affine_charts`; there are no axioms, unsafe/opaque/extern declarations, or hollow definitions. The concrete `FlatDescentChart` data and its predicates contain no `sorry`.

3. **Statement and node review.** Checked the existing theorem statement against the repository and its DAG node, and checked the new chart theorem and structure against their node statements. The chart theorem is a genuine affine reduction: it does not restate the parent theorem or assert eventual flatness, and the structure is concrete ring data rather than a witness selected from an unproved existence result. The new node records its source, proof narrative, dependencies, and Lean declarations.

4. **Proof route and pruning.** The parent proof follows the chart reduction and the existing eventual-flatness ring theorem, then takes a finite common upper bound. Its imports and DAG proof dependencies match that route; no old dependency was removed, and no unit route is bypassed. The chart theorem's imports are the Mathlib interfaces needed by its public signatures and predicates.

5. **Edge cases and unit route.** Reviewed the empty-chart/source case and the directed upper-tail construction, including the finite-image common-bound argument. These handle `n = 0` and preserve the `sk-thm-p1` unit route. No statement-disputed issue or forced adaptation was found.

No changes were needed during this second reading.
