## What changed

Replaced the single hole in `Sheaf.Paper.FiniteStructureMultiplicationLift` by a complete
Lean proof from existence of a multiplicative product and faithful tensor tests. Its signature,
visibility, existing public imports, definitions and original docstring are unchanged. Added
proof-only imports of `Sheaf.Paper.FiniteStructureProductExists` and
`Sheaf.Paper.FiniteStructureTensorTestsFaithful`.

The proof equates `braiding ≫ μ` and `μ` using the square test and commutativity in each
`O_Yn`. It equates `(μ ▷ G) ≫ μ` and `associator ≫ (G ◁ μ) ≫ μ` using the cube test and
associativity in each `O_Yn`. Evaluating these morphism identities with the proved tensor-section
formulas gives the exact section laws in the target. Two products satisfying its final
multiplicativity clause give the same adjoint images on elementary tensors; the square test
then proves their equality. No injectivity assertion about sections on an arbitrary open is used.

Added three modules, one public theorem each:

- `Sheaf.Paper.FiniteStructureProductExists`: the one remaining existence step, with a complete
  proof plan in its docstring, including the reduced product, tensor-composition equation,
  compatibility calculation, completion lifting and section formula.
- `Sheaf.Paper.FiniteStructureTensorPowersSupported`: proved coherence and proper support of
  the square and cube. The proof uses coherent finite affine sections, the affine tensor
  comparison and finite-type criterion. It restricts annihilating ideal sections to contained
  affine opens, proves tensor annihilation by induction, glues with the sheaf condition, and
  applies the closed-immersion annihilation theorem and proper-support characterization.
- `Sheaf.Paper.FiniteStructureTensorTestsFaithful`: proved the square and cube tests. Affine
  tensor surjectivity and tensor induction establish equality of composite morphisms. The
  pinned adjunction and cancellation of `ψ` give equality of their reductions. The Hom
  uniqueness clause of Grothendieck existence then gives equality of the original maps.

The new support and tensor-test helpers are entirely proved from existing library statements;
all private helpers are proved. Proof-dependency imports of the remaining existence step are
included as the plan for its next worker. Updated the original node's proof, proof dependencies
and proof origin, and supplied the three new nodes. No interface change or forced adaptation.

Sources read: Stacks [09ZT](https://stacks.math.columbia.edu/tag/09ZT),
[088F](https://stacks.math.columbia.edu/tag/088F),
[0CYS](https://stacks.math.columbia.edu/tag/0CYS),
[01XZ](https://stacks.math.columbia.edu/tag/01XZ), and
[01I8](https://stacks.math.columbia.edu/tag/01I8), plus the library's existing declaration
signatures and proofs. The new statements were checked on zero modules, empty schemes,
empty opens, zero ideals and the complete-unit-ideal case. None excludes those cases.

All four delivered modules compile through `lcompile.py --all` in import order. Single-file
compiles were also used during development; no global library build was run.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.finite_structure_multiplication_lift`
(node `lem-weil-pbc-finite-structure-multiplication-lift`). No `sorry` remains in that module.

Added exactly one hole:
`AlgebraicGeometry.finite_structure_product_exists`
(node `lem-weil-pbc-finite-structure-product-exists`), with body exactly `:= by sorry`.
It asserts existence of a map preserving all reduced products, without ring laws or uniqueness.
This is strictly the existence/multiplicativity part of the original argument. The Lean proof
supplies the omitted laws and uniqueness; it is not a renamed copy of the original conclusion.

Also proved the new public declarations
`AlgebraicGeometry.finite_structure_tensor_powers_supported`
(node `lem-weil-pbc-finite-structure-tensor-powers-supported`) and
`AlgebraicGeometry.finite_structure_tensor_tests_faithful`
(node `lem-weil-pbc-finite-structure-tensor-tests-faithful`). Their modules contain no `sorry`.

This is a decomposition: one original hole closed, one lower hole added, net zero declaration
holes before any import-closure effects. The proof still uses existing library declarations
whose dependencies contain `sorry`; it is not claimed axiom-free through that entire closure.
No hole is placed in a definition, a private helper or the main proof.

## No longer needed

None of the original module's imports was removed; they form its existing public interface.
No original planned mathematical dependency is globally pruned. The support/coherence
steps now occur in the proved tensor-powers helper; the faithfulness step occurs in the proved
tensor-tests helper; tensor pullback, base change and fullness remain needed for the existence
step. The symmetric monoidal tensor formulas are used in the original module's proof.

The original node's direct proof dependencies are now the two new helper nodes and the
symmetric-monoidal node. The earlier dependencies remain needed beneath those helpers,
including the proper-support, affine tensor, affine finite-type, coherence, tensor-pullback,
base-change, composition-comparison and Grothendieck-existence nodes. This reorganization is
not a claim that their modules can leave the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the target statement was found; its statement is unchanged and the
unit route is preserved. The item is below the unit's own realized statements and steps.

One interface distinction matters to the remaining existence proof. The target pins `c` to
`tensorPullbackCompositionIso`, whereas `grothendieck_existence` currently requires a
comparison made from `Classical.choice (nonempty_tensorPullbackComp ...)`. Equality of those
choices must not be asserted by reflexivity or proof irrelevance: a bare `Nonempty` theorem does
not pin its witness. The existing canonical-comparison change record already documents this
issue for the algebra-operations caller. Our faithfulness proof avoids the distinction: it
chooses the comparison required by Grothendieck existence solely to make the reductions of an
already existing morphism a compatible family by naturality. It never identifies it with the
pinned comparison or uses it to transport products. The next worker on ProductExists must
handle canonical fullness through the formal-completion interfaces or a justified comparison
bridge; its docstring states the mathematical argument with the genuine canonical comparison.

A tempting stronger section-injectivity claim is false: for a complete discrete valuation
ring A and I its uniformizer ideal, take X = Spec A, G = O_X and U = D(uniformizer).
All adic reductions over U are empty, so their adjoints cannot detect sections of G(U).
The delivered statement only detects global morphisms. Its proof first compares whole
composite sheaf morphisms and then uses completion faithfulness, so this edge case is valid.

The local `literature/stacks-project/coherent.tex` named by the old node is absent on this
machine. The corresponding primary Stacks pages were read directly, and the new nodes record
those sources. LeanSearch returned Internal Server Error; this is recorded in searches.jsonl.
LeanFinder, Loogle, ripgrep and source-library searches were used instead. No exact theorem
covering the requested lifting statement was found; existing results are used for each
support and faithfulness step.

## New nodes

`lem-weil-pbc-finite-structure-product-exists`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-structure-product-exists.json`, records
only existence and multiplicativity of the lifted product. Its only hole is the public theorem
in `lean/Sheaf/Paper/FiniteStructureProductExists.lean`. This is the remaining parallel item.

`lem-weil-pbc-finite-structure-tensor-powers-supported`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-structure-tensor-powers-supported.json`,
records the proved square/cube coherence and proper-support assertion in
`lean/Sheaf/Paper/FiniteStructureTensorPowersSupported.lean`. It needs no adic completeness,
separatedness or quasi-compactness, and does not construct multiplication.

`lem-weil-pbc-finite-structure-tensor-tests-faithful`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-structure-tensor-tests-faithful.json`,
records the proved global morphism tests in
`lean/Sheaf/Paper/FiniteStructureTensorTestsFaithful.lean`. It needs no compatibility of ψ,
finiteness of the maps from Y_n or ring structure on G. It is applied three times in the
original proof: symmetry, associativity and uniqueness.

No change record was needed.

## Second reading by A2

1. Compared the delivered multiplication-lift module with the repository version. Existing declarations and the target signature are byte-for-byte unchanged; only proof-only imports and the proof body changed. Verdict: pass.

2. Compiled all four delivered modules with `lcompile.py --all`; compilation succeeds. The multiplication-lift module has no `sorry`, and the only remaining `sorry` is the named existence theorem `AlgebraicGeometry.finite_structure_product_exists`, whose node and docstring are present. No forbidden declarations or hollow definitions were found. Verdict: pass.

3. Reviewed the split statements and searched the library and Mathlib-facing search tools. The support and faithfulness declarations are strictly smaller than the target, while product existence contains only the existence and multiplicativity clause needed by the target. Edge cases listed above remain admitted by the statements. Verdict: pass.

4. Checked the proof route against the unit `sk-thm-p1`: the target still uses the product-existence step and the tensor-test step; the support/coherence work is encapsulated below those steps. Removed no imports because all existing public imports remain part of the interface. Verdict: pass.

5. Compared all changed node metadata with the Lean declarations. The target node proof and dependencies follow the proof, and each new node has matching statement, source, proof plan, Lean record, chapter and unit metadata. Verdict: pass.

Changed in this second reading: added this review section only; no Lean declarations, statements, definitions, imports, or DAG metadata were altered.
