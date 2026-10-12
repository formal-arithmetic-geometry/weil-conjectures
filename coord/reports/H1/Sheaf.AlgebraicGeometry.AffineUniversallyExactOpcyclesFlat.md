## What changed

Replaced the proof hole in `Sheaf.AlgebraicGeometry.AffineUniversallyExactOpcyclesFlat`
with a complete compiled reduction. Evaluate the complex on the top open, derive term
flatness from the original affine-local hypothesis (including the scalar-action equality),
apply the existing `Module.Flat.opcycles_of_exactAt`, and transfer its conclusion back.
The existing theorem signature, docstring and both public imports are unchanged.
Added three proof-only imports: `Sheaf.Algebra.Homology.FlatOpcyclesTorCriterion`,
`Sheaf.AlgebraicGeometry.AffineUniversalTensorExact`, and
`Sheaf.AlgebraicGeometry.AffineOpcyclesFlatFromSections`.
Updated the original node's proof, proof_deps and proof_origin to match this reduction.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.affine_opcycles_flat_of_universally_exact`
(node `lem-pc-affine-universally-exact-opcycles-flat`). No sorry remains in the item module.
This is a decomposition, not a completed proof from standard axioms: two lower holes are added,
and the proof also uses the existing holed `Module.Flat.opcycles_of_exactAt`
(node `lem-pc-module-flat-opcycles-tor-criterion`).

Every added sorry, each the entire proof of its public named theorem:

- `AlgebraicGeometry.Scheme.Modules.affine_universal_tensor_exact`, node
  `lem-pc-affine-universal-tensor-exact`, module
  `Sheaf.AlgebraicGeometry.AffineUniversalTensorExact`.
- `AlgebraicGeometry.Scheme.Modules.affine_opcycles_flat_from_sections`, node
  `lem-pc-affine-opcycles-flat-from-sections`, module
  `Sheaf.AlgebraicGeometry.AffineOpcyclesFlatFromSections`.

The first comparison assumes no flatness and proves tensor exactness in an arbitrary degree;
it does not assert opcycles flatness. The second has no universal base-change hypothesis and
only assumes quasi-coherence of the two cokernel terms and flatness of module opcycles.
Neither restates the original theorem. There are no added definitions or chosen data.
The empty affine scheme, zero ring, zero complex, N=0 and zero cokernel were checked against
the two arguments. No boundedness or finite-presentation assumption is used.
All three Lean modules compile locally with no warnings.

## No longer needed

No imports removed, and no module is claimed globally pruned. The original direct proof
edges to `def-pc-base-change`, `def-pc-tensor-complex-sheaves`,
`lem-pc-affine-sections-flat-over-base`, `lem-weil-pbc-affine-tilde-gamma-adjunction`,
and `lem-weil-pbc-spec-module-tilde-sections` are replaced by the two comparison nodes.
Affine equivalence, localization and base change remain needed below those nodes;
this is encapsulation rather than global pruning. The existing module Tor criterion is retained.
The full sheaf tensor total-complex definition is not directly used by this proof.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically appropriate. Its affine equivalence and module
Tor criterion statements alone do not expose either the square-zero tensor exactness test
or the affine sheaf flatness transfer; those comparison steps are now precisely stated.
The original declaration is not disputed, and no existing statement or definition changes.
LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle, direct rg of both
library roots and Mathlib, and blueprint searches found ingredients but no exact comparison.
The referenced blueprint source files are absent in this machine's read-only literature
checkout; the unit record supplies its text, and the Stacks pages 0653 and 01IB were read online.
The unit's realized lists are empty and the original square-zero/Tor/sheafification route is kept.

## New nodes

`lem-pc-affine-universal-tensor-exact`: original steps 1--2, in a new module with one theorem.
It reduces universal scheme pullback vanishing to exactness after tensoring the module
complex, without a term flatness hypothesis, using the explicit trivial square-zero algebra
and its additive summand retraction. Complete proof is in the docstring and node.

`lem-pc-affine-opcycles-flat-from-sections`: original step 4, in a new module with one theorem.
It transfers flat module cokernels to the affine-local sheaf condition using the affine
counit, preservation of cokernels, localization, prime-local flatness and transitivity.
Complete proof is in the docstring and node. Neither new node bypasses a blueprint unit.
No change records or forced adaptations are needed.

## Second reading by H1

1. **Diff and interfaces.** Compared the delivered item module with the repository version.
   The theorem signature, docstring, and existing public imports are byte-for-byte unchanged;
   only proof imports and proof text were added. The two new modules introduce the declarations
   recorded by their nodes, and no existing declaration is altered. Verdict: pass.
2. **Compilation and axioms.** Compiled all three delivered modules with `lcompile.py --all`.
   They compile without errors or warnings. The item has no `sorry`; the two explicitly split
   theorems contain the only remaining `sorry`s, each named and documented above. Axiom checks
   show only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from those split nodes.
   Verdict: pass.
3. **Statements and new nodes.** Read both split-off statements against their proofs and
   edge cases (zero module, zero complex, empty affine scheme, and degree zero). Each is a
   strictly smaller comparison lemma, has a source, matching Lean declaration, and matching
   DAG node; neither merely restates the target nor duplicates an existing library result.
   Verdict: pass.
4. **Pruning and route.** The target proof uses the module Tor criterion and exactly the two
   new comparison lemmas. Its proof and `proof_deps` record this route; no import can be removed
   from the delivered modules, and the unit route is retained. Verdict: pass.
5. **Delivery checks.** Ran the stage-3 dry run after this report update; the only former
   failure was the missing second-reading section, now repaired. No definition, target
   statement, or forced adaptation was changed. Verdict: pass.

Changed in this second reading: added this review section to satisfy the delivery contract;
no Lean code or DAG content required repair.
