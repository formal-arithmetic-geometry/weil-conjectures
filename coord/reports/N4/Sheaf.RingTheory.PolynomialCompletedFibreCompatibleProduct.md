## What changed

Proved `Polynomial.completed_fibre_compatible_product` in
`Sheaf.RingTheory.PolynomialCompletedFibreCompatibleProduct`, without changing its signature,
visibility, or existing docstrings. The proof constructs the polynomial-extension finiteness
instance, applies the existing completion decomposition, composes Mathlib tensor equivalences,
proves the discarded fibres subsingleton, restricts the product, and enumerates the retained
primes by `Fin n`. The empty retained subset is handled by the same bijective restriction map.

Added proof imports of `Mathlib.RingTheory.PolynomialAlgebra`,
`Mathlib.RingTheory.Polynomial.Basic`, and `Mathlib.RingTheory.TensorProduct.Finite`.
Replaced the completion wrapper import with its decomposition module. Updated the item's DAG
proof and dependencies to record this route. All original public imports are preserved.

## Proved and sorry left

Closed one hole: `Polynomial.completed_fibre_compatible_product`
(node `lem-weil-pbc-polynomial-completed-fibre-compatible-product`).
No holes remain in this module and no holes or declarations were added elsewhere.
The proof uses existing completion-decomposition declarations and their existing dependency
holes; it does not claim to close those dependencies.

## No longer needed

Removed `Sheaf.RingTheory.CompletionFiniteExtension`: its stronger combined theorem is replaced
by `Sheaf.RingTheory.CompletionFiniteExtensionDecomposition`. This proof does not need the
wrapper node `lem-weil-pbc-completion-finite-extension`, nor the wrapper-only modules
`Sheaf.RingTheory.FiniteAfterCompletion`,
`Sheaf.RingTheory.CompletionFiniteExtensionTensor`,
`Sheaf.RingTheory.ExtendedCompletionModuleReduction`, and
`Sheaf.RingTheory.FiniteOverCompleteRing`. The source-import closure difference is exactly
these five modules (the wrapper, the tensor theorem, and the three additional modules).
Their nodes are `lem-weil-pbc-completion-finite-extension`,
`lem-weil-pbc-completion-finite-extension-tensor`,
`lem-weil-pbc-extended-completion-module-reduction`,
`lem-weil-pbc-finite-after-completion`, and `lem-weil-pbc-finite-over-complete-ring`. They may still be needed by other library modules; pruning here is local to this
item's route.

Removed the redundant direct import `Mathlib.RingTheory.TensorProduct.Maps`, already publicly
provided by `Mathlib.RingTheory.TensorProduct.Pi`. No binary-product lemma is used:
`lem-weil-pbc-algebra-tensor-product-distributes-product` is replaced by the existing finite
product tool node `lem-weil-pbc-tensor-finite-product`, in its Mathlib algebra form
`Algebra.TensorProduct.piRight`.

## Where the brief, the DAG or earlier work was wrong

The planned distribution dependency stated only binary products. The proof needs finite
dependent products, including the empty product; Mathlib's `Algebra.TensorProduct.piRight`
provides exactly that form. The existing node `lem-weil-pbc-tensor-finite-product` records the
underlying finite-product tensor equivalence, and its search record names the algebra form.

The full completion theorem also returns a tensor-completion equivalence that this argument
does not use. Its decomposition theorem is sufficient. No unit statement or unit proof step
is bypassed: this node is below the unit's realized statements and steps.

Searches run with `msearch.py`: LeanFinder for base change of fibres through finite products
of local completions, and Loogle for `Algebra.TensorProduct.cancelBaseChange`; direct `rg`
searches inspected the tensor, polynomial-base-change, integral-extension, residue-field, and
localization APIs. The available Stacks source tree did not contain `more-algebra.tex`, so
Tag 07PU was read from https://stacks.math.columbia.edu/tag/07PU. Its displayed decomposition
matches the argument. All constructions and the contraction and zero-factor calculations
are checked by Lean.

## Second reading by N4

1. PASS: compared the sole delivered module with the repository by `diff`, and checked
   the existing theorem signature byte for byte through `:= by`. The signature,
   visibility, definitions, and existing docstrings are unchanged. Only proof imports
   and the theorem body change; no change record or forced adaptation is needed.
2. PASS: compiled the module locally with `lcompile.py`, with no errors or warnings.
   Independently compiled a scratch copy with `#print axioms
   Polynomial.completed_fibre_compatible_product`: exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`, the last from existing completion dependencies.
   There is no `sorry` or forbidden declaration in the delivered module, and no new
   definition or data chosen from an unproved existence theorem is introduced.
3. PASS: no statements are split off, and no new declarations, modules, nodes, or holes
   are added. Read the contraction, tensor-compatibility, and zero-factor arguments.
   The restriction map is injective by subsingleton discarded factors and surjective
   by extension by zero; this also works when the retained subset is empty.
4. PASS: inspected the completion decomposition and the Mathlib polynomial, finite
   tensor, integral-extension, and finite-product APIs; independently searched the
   repository and upstream ring-theory sources and used `msearch.py grep` with
   completed-fibre and tensor-product queries. No shorter existing theorem giving
   the compatible selected-prime presentation was found. Each proof import supplies
   a used construction or instance; all new imports are private. The old dependencies
   removed are the completion wrapper and binary-product node, both reported above.
   Independently recomputed the library import-closure difference: exactly the five
   modules listed under No longer needed. Read `dag/units/sk-thm-p1.json`: this item
   is below its realized statements and steps; none is bypassed or changed.
5. PASS: the only changed node fields are `proof`, `proof_deps`, and `proof_origin`.
   Read each dependency's statement and Mathlib match or Lean declaration; they
   match the written argument. The union of the steps' `uses` equals `proof_deps`.
   The completion decomposition supplies the only project theorem invoked; the
   integral and tensor steps use their recorded Mathlib tools.

Second reading changed only this report: added the independent review and explicit
axiom result. The Lean proof and DAG needed no repair. Closed one existing hole,
`Polynomial.completed_fibre_compatible_product`; added zero holes. This is a proof
of the item relative to existing open dependencies, not a decomposition into new holes.
