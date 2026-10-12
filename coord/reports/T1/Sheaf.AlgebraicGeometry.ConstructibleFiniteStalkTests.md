## What changed

Proved `AlgebraicGeometry.Scheme.exists_finite_stalk_tests_of_constructible` in
`lean/Sheaf/AlgebraicGeometry/ConstructibleFiniteStalkTests.lean`, with its signature unchanged.
The proof chooses the images of the generic points of an irreducible lisse stratification.
It transfers stalk finiteness through the inverse-image/forget comparison and the two stalk
isomorphisms, and uses the existing generic-stalk criterion to prove each restricted map mono.
Finally it lifts the algebraic-closure points into strata and cancels stalk monomorphisms;
geometric-stalk extensionality proves the original map mono.

Added the proof-only import `WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism` for
its already-proved `Scheme.exists_comp_eq_of_mem_range`. The two new private helpers are
fully proved: `locallyConstant_of_iso` transports the same trivializing cover, and
`geometricPoint_lift` obtains a lift and identifies its underlying point using the immersion's
injectivity. No public signature, definition, or public import changed.
Updated the item's node proof and proof origin to describe the implemented argument.
The unit `sk-prop-sf-cbc` has empty `realized.statement` and `realized.steps`; no unit route
is bypassed. All six original proof dependencies remain used.

Searches: LeanFinder returned topological-sheaf stalk criteria, with no finite geometric-test
criterion. Loogle returned the generic-point API. Mathlib grep and searches in
`lean/WeilConjectures` and `lean/Sheaf` located the existing point-lifting, stalk comparison,
constancy-under-isomorphism, and geometric-stalk extensionality lemmas. These close all glue;
no new intermediate statement is needed.

## Proved and sorry left

The item's sole original sorry is closed:
`AlgebraicGeometry.Scheme.exists_finite_stalk_tests_of_constructible`
(node `lem-weil-pbc-constructible-finite-stalk-tests`). Both private helpers are also proved.
There are no sorries left in the delivered module, and this delivery adds no sorry.

The proof depends on these already-stated, untouched theorems with sorry:

- `AlgebraicGeometry.Scheme.exists_irreducible_lisse_stratification`
  (`lem-weil-pbc-irreducible-lisse-strata`).
- `AlgebraicGeometry.Scheme.mono_of_mono_generic_stalk`
  (`lem-weil-pbc-lisse-generic-kernel`).
- `AlgebraicGeometry.etaleInverseImageAlgebraicStructures`
  (`lem-weil-pbc-etale-inverse-image-algebraic-structures`).

The delivered theorem is therefore a complete Lean reduction to the existing statements,
not an assertion that its transitive dependency closure is sorry-free.
The local compile passes without warnings. The finite index type also handles the empty
scheme without a separate nonemptiness assumption; no hypothesis on the target sheaf was added.

## No longer needed

No imports, nodes, or modules are pruned: every original import and all six proof dependencies
are used. The planned kernel-zero argument is unnecessary as an argument step; direct
stalk cancellation and joint faithfulness replace it. Exactness is still used through stalks'
finite-limit preservation, and conservativity through geometric-stalk extensionality.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The original last proof step was longer
than needed: `Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint` gives the cancellation
argument directly. The higher coefficient universe requires explicit shrinking of filtered
colimit preservation and AB5 from size u + 1 to size u; both are existing Mathlib lemmas.
The lifting is a scheme-morphism factorization supplied by the existing residue-field lemma,
not an inference from topological containment alone.

## Second reading by T1

1. **Statements and interfaces — pass.** I diffed the delivered module against the repository
version. The existing theorem signature and all existing declarations are byte-for-byte
unchanged; the only source change is a proof-only import, two private proved helpers, and the
proof body. The node's Lean statement is unchanged.

2. **Proof and axioms — pass.** The module compiles with `lcompile.py` without errors or
warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`
declarations in the delivered module; the only open assumptions are the pre-existing imported
theorems listed above. The helpers contain ordinary proofs and no hollow definitions.

3. **Split-off statements — pass.** No public split-off theorem or new node was added. The two
private helpers are local proof infrastructure, and searches reported no existing declaration
that would make a missing intermediate statement necessary.

4. **Route and pruning — pass.** The proof follows the finite irreducible lisse stratification
route, uses the existing generic-stalk criterion and stalk comparisons, and then uses direct
geometric-stalk cancellation. The proof-only universal-homeomorphism import is needed for the
point lift. All original imports and six proof dependencies remain used, so no pruning is due;
the unit route is retained.

5. **DAG agreement — pass.** The item's node proof steps, dependencies, and proof origin now
describe the implemented generic-point lifting and cancellation argument. The Lean declaration,
module, chapter, unit, and statement fields agree with the delivered source.

**Changes made during second reading:** none were required after compilation and interface/DAG
comparison.
