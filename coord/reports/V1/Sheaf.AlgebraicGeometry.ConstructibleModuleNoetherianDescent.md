## What changed

Proved `AlgebraicGeometry.Etale.exists_noetherian_descent` in
`Sheaf.AlgebraicGeometry.ConstructibleModuleNoetherianDescent`, without changing its signature.
Added proof-only imports of `Mathlib.CategoryTheory.Presentable.Directed`,
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`, and
`Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent`.

The proof takes the existing Noetherian approximation of X, reindexes its cofiltered
category via a final functor from a nonempty directed partial order, and uses the initial
left-opposite functor to retain the same limiting apex X. All stages are Noetherian by
the approximation's proved instance, and hence qcqs. Apply the existing module-sheaf
descent theorem to this cone and take its stage and sheaf as the existential witnesses.
The pullback isomorphism has exactly the required morphism, coefficient category, and
orientation, by definitional equality. The DAG proof was adjusted to match this assembly.

The module compiled cleanly with lcompile.py. All imports are used: the two original
public imports support the statement, and the three new imports provide the directed
reindexing, approximation, and descent declarations respectively. No definitions,
statements, or other modules were changed. The sk-thm-p1 unit route is unchanged.

## Proved and sorry left

Proved the item's only sorry, `AlgebraicGeometry.Etale.exists_noetherian_descent`
(node `lem-weil-pbc-constructible-module-noetherian-descent`). No sorry remains in the
item and no new sorry or node was added.

The proof intentionally depends on the existing theorem
`AlgebraicGeometry.Scheme.exists_constructible_etaleModuleSheaf_descent`
(node `lem-weil-pbc-constructible-module-limit-descent`), which still contains sorry
in its existing module. This is the next mathematical obligation, not a new statement
or a renamed copy of this item.

## No longer needed

No existing imports were removed. The direct DAG dependency
`lem-weil-pbc-limit-affine-transition` and its module
`Sheaf.AlgebraicGeometry.LimitAffineTransition` are unnecessary for this proof:
the approximation already supplies its limit cone, and initial reindexing preserves it.
They are not imported here. This is only pruning of this item's direct edge; the existing
descent theorem may still need affine-limit results in its own proof.
All other original direct proof dependencies remain used, either through their recorded
Mathlib declarations, the approximation structure and its existing instances, or the
constructible-module descent theorem. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement defect was found. Step 2 needlessly cited separate existence
of an affine-transition limit: its limit is already supplied by step 1 and transported
by initial reindexing. The repository's local literature copies are absent; the source's
first paragraph was checked at https://stacks.math.columbia.edu/tag/09Z7, and the unit
was checked from dag/units/sk-thm-p1.json. LeanFinder returned generic sheaf-of-modules
finite-presentation results, Loogle found no matching Noetherian/etale declaration, and
local searches found no shorter compatible theorem. The upstream candidate uses a
different constructibility predicate and was not used.

## Second reading by V1

1. **Visible declarations.** Compared the delivered module with the repository version. The theorem
   signature and all existing declarations are byte-for-byte unchanged; only proof-only imports and
   the theorem proof differ. The DAG statement is unchanged.
2. **Proof validity.** Compiled the module and the sandbox import closure with `lcompile.py`.
   There are no `sorry`s in this module, no forbidden declarations, and the theorem's only additional
   axiom dependency is `sorryAx` from the pre-existing imported descent theorem; the remaining axioms
   are `propext`, `Classical.choice`, and `Quot.sound`.
3. **Statements and dependencies.** No new statements or split-offs were added. The existing
   constructible-module limit-descent theorem is used directly; it is a distinct lower-level node,
   not a restatement of this item. The approximation import is required because it defines
   `Scheme.nonempty_noetherianApproximation` and its stage instances.
4. **Route and pruning.** The proof keeps the unit route: Noetherian approximation, directed
   reindexing, Noetherian/qcqs stages, and module-sheaf descent. The separate affine-transition-limit
   result is not used as a proof step; the approximation's own limit cone is transported by the
   initial reindexing. No further imports can be removed without losing the approximation or descent
   declarations.
5. **DAG agreement.** The node's `proof`, `proof_deps`, and `proof_origin` match the Lean proof,
   including the use of `G.leftOp`, the transported limit cone, and the existing descent theorem.
   The unit's realized route is preserved.

I corrected the report's import/pruning wording: `AffineTransitionLimit` remains a necessary
proof-only import for the Noetherian approximation API, while no separate affine-limit theorem is
used. No Lean or DAG changes were needed.
