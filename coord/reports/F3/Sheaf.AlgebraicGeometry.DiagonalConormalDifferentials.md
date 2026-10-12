## What changed

`Sheaf.AlgebraicGeometry.DiagonalConormalDifferentials` now proves
`AlgebraicGeometry.diagonalConormal_iso_relativeDifferentials` from two strictly smaller
statements in new modules, following Stacks Tag 08S2 as read at
https://stacks.math.columbia.edu/tag/08S2. The theorem's signature and both object definitions
are unchanged. The proof constructs the comparison with the existing universal property,
proves the adapted affine opens form a basis, applies Mathlib's basis isomorphism criterion,
reflects the isomorphism to module sheaves, and inverts it.

New module `Sheaf.AlgebraicGeometry.DiagonalConormalDerivation` states existence of the
relative difference derivation, with a precise sectionwise normalization using the actual
kernel inclusion and the canonical tensor-pullback unit. The predicate
`AlgebraicGeometry.IsDiagonalConormalDerivation` contains no postponed data or proof.
This statement asserts existence of a normalized derivation, not invertibility.

New module `Sheaf.AlgebraicGeometry.DiagonalConormalAffineComparison` states bijectivity
of the induced map on one affine chart, assuming a normalized derivation. It neither
constructs the derivation nor asserts a global isomorphism. Its proof task includes the
restriction of the actual kernel to the affine closed diagonal, comparison of the section
maps, and the ring formula already in Mathlib. Both new theorems have complete source-based
proof descriptions, exactly `by sorry` proofs and matching nodes.

The main module replaces its direct proof import of `AffineConormalSections` by the new
affine-comparison module and uses Mathlib's sheaf basis criterion through transitive imports. The existing public
imports remain. All three modules compile without warnings with `lcompile.py --all`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.diagonalConormal_iso_relativeDifferentials`
(node `lem-sc-smooth-proper-diagonal-conormal-differentials`). No sorry remains in the item.

Added exactly two holes:

- `AlgebraicGeometry.exists_diagonalConormalDerivation`, in
  `Sheaf.AlgebraicGeometry.DiagonalConormalDerivation`, node
  `lem-sc-diagonal-conormal-derivation-exists`.
- `AlgebraicGeometry.diagonalConormalComparison_bijective_on_affine`, in
  `Sheaf.AlgebraicGeometry.DiagonalConormalAffineComparison`, node
  `lem-sc-diagonal-conormal-affine-comparison`.

This is a decomposition: one upper hole closed and two lower holes added, not a completed
sorry-free proof of the mathematical theorem. Existing holes in imported modules are unchanged.
The combining proof is complete Lean and does not use a restatement of the original theorem.

## No longer needed

The main file's direct `Sheaf.AlgebraicGeometry.AffineConormalSections` import is replaced
by the affine comparison module. That existing theorem is still required below both new
nodes; no existing dependency node or module is pruned from the closure.
The ring-level `lem-sc-kahler-differentials-diagonal-ideal` remains needed in the local
comparison and is realized by Mathlib's definitions and `KaehlerDifferential.D_apply`.
All three old direct proof dependencies are removed from the parent's `proof_deps`:
`lem-weil-pbc-affine-conormal-sections`,
`lem-sc-kahler-differentials-diagonal-ideal`, and
`def-weil-pbc-kahler-differentials`. The first two remain below the new nodes; the
third remains the ring-differentials definition used by the diagonal cotangent
calculation. The direct `Mathlib.Topology.Sheaves.SheafCondition.Sites` import was
also removed because transitive imports provide the criterion. This is relocation of
dependencies, not pruning from the closure.
No new general sheaf-gluing theorem or quasi-coherence hypothesis is needed: the main
proof uses the existing Mathlib basis criterion on abelian sheaves.

## Where the brief, the DAG or earlier work was wrong

The DAG treats compatibility and sheaf gluing as elementary but gives no Lean map or
normalization to glue. Its affine conormal dependency concerns the ideal `i.ker.toModules`
of a closed immersion. Here the definition uses the actual categorical kernel of the
possibly nonclosed diagonal. The restriction bridge to a closed affine diagonal must be
proved; it is explicitly included in the new local comparison task, not silently assumed.
The source Tag 08S2 constructs a global difference derivation first and then proves local
bijectivity. That route retains the same affine conormal and ring calculations and the
unit's diagonal identification; the unit record has no separately prescribed realization
of these internal steps. No target, existing statement, or definition was changed.

Edge-case review of the new statements: for an identity morphism, the diagonal ideal and
relative differential module are zero, the normalized derivation is zero, and the chart
map is the bijection between zero modules. For `Spec(R[t]) → Spec(R)` the normalization
sends `dt` to `1 ⊗ t - t ⊗ 1`, matching Mathlib's `D_apply`; the sign and orientation agree.
Empty opens give zero section modules and impose no nonemptiness hypothesis. For a
nonseparated morphism the construction uses the neighbourhood of Tag 01KJ, with no
separatedness or quasi-compactness assumption. In the normalization, its three open
inclusions imply `δ⁻¹W = U` since `δ ≫ p₁ = id`, so the section restriction is well typed
and does not impose an unintended larger-open condition.

LeanSearch returned HTTP Internal Server Error for both new statements, recorded as
unavailable. LeanFinder returned ring or general presheaf constructions, not either
scheme-level statement; Mathlib grep found no conormal derivation. The Mathlib ring
calculation is already present. Blueprint searches for both new statements returned no
matches, and full DAG/library text searches found only the original comparison and its
users, not these intermediate declarations.

## New nodes

`lem-sc-diagonal-conormal-derivation-exists` records the source's square-zero extension
construction and the sectionwise normalization. Its module is
`lean/Sheaf/AlgebraicGeometry/DiagonalConormalDerivation.lean`; the node also records the
normalization predicate among its realized declarations. It is strictly the map-construction
part of the argument and contains no assertion of an isomorphism.

`lem-sc-diagonal-conormal-affine-comparison` records the single-chart calculation. Its
module is `lean/Sheaf/AlgebraicGeometry/DiagonalConormalAffineComparison.lean`. It assumes
normalization, identifies the two affine section modules and their generator formula,
and concludes bijectivity on that chart only.

The parent node's proof, proof dependencies and proof origin are updated to the actual
Lean route. No change records are needed: existing interfaces are unchanged and both new
modules are imported for proofs only.

## Second reading by F3

1. Compared the delivered main module with the repository by `diff`. Verdict: pass.
   Its existing theorem signature, universe, variables, namespace and both public
   imports are unchanged. Neither existing object definition is delivered or altered.
   The only additional visible declarations belong to the two declared new modules.
   Restored the existing theorem docstring verbatim; the actual reduction is described
   in this report and the updated parent node. No statement change record is needed.
2. Compiled all three modules through `lcompile.py --all`: no errors or warnings.
   Inspected all definitions and every proof. Verdict: pass with the two reported
   theorem holes. No forbidden trust mechanism or definition hole occurs. In a scratch
   copy, `#print axioms` for the normalization predicate gave only `propext`,
   `Classical.choice`, `Quot.sound`; both new theorems and the main theorem additionally
   gave `sorryAx`, as expected for this decomposition. The selected adjunction's unit
   is fixed sectionwise by `exists_tensorPullbackAdjunction`; the predicate never
   chooses an arbitrary conormal object. The existential derivation is eliminated
   inside the theorem proof, not used to define data in the library.
3. Read the full new statements, docstring proofs and nodes against Stacks 08S2 and
   01KJ. Verdict: pass. The difference formula gives a derivation; the affine lemma
   assumes that formula and proves only local bijectivity. Neither restates the global
   item. Checked identity morphisms, polynomial affine charts (including the sign),
   empty opens and nonseparated morphisms. The normalization is not vacuous on adapted
   affine charts: the projection difference restricts to zero on the diagonal and
   therefore lifts to the actual kernel sections. For arbitrary displayed U,W,
   the three open inclusions imply the diagonal inverse image of W equals U.
   Independent LeanFinder searches for a pullback-of-diagonal-kernel comparison and
   differences of square-zero splittings found general presheaf or ring lemmas, not
   these scheme statements. Mathlib/upstream/local `rg` and `msearch.py grep` found
   no matching scheme result; existing differential restriction and affine formulas
   are already used by the planned local proof. Closing either remaining theorem
   requires the scheme restriction/kernel bridge, not a short application overlooked
   by the first worker.
4. Read the combining proof from the top, the original imports/dependencies and
   `dag/units/sk-thm-picard-duality.json`. Verdict: pass. It uses the existing universal
   property and Mathlib's basis criterion; no extra gluing or quasi-coherence hole is
   introduced. Public imports supply signature/definition ingredients, and the new
   main imports are proof-only. Removing the Sites import in a scratch compilation
   succeeded, so the redundant direct import was removed. The affine-conormal imports retain the planned
   dependencies of the open tasks. The unit's realized statement/step arrays have no
   additional prescribed nodes for this internal argument and are unchanged; its
   diagonal identification remains the same parent declaration. Expanded `No longer
   needed` to enumerate all three old direct parent dependencies and distinguish their
   relocation from closure pruning. No existing module is pruned.
5. Compared the parent JSON with the repository: only `proof`, `proof_deps` and
   `proof_origin` differ. Checked both new nodes' statement, Lean signature, docstring
   tag, sources, steps/dependency union, searches, creation record, chapter, unit,
   blueprint provenance and Lean realization. Verdict: pass. The parent records the
   actual construction, local comparison, basis/reflection and inverse. The new nodes
   accurately include the restriction bridge from the actual categorical kernel to
   the closed affine diagonal, which the old affine theorem alone does not supply.

Second-reading changes: removed the redundant Sites import, restored the original
theorem docstring and completed the pruning report; no Lean statement or proof was changed. One original hole is closed
by a real combining proof and two strictly smaller holes remain: a decomposition
with net holes closed minus added equal to -1, not a sorry-free theorem.
