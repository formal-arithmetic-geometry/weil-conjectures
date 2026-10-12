## What changed

Completed the reduction of
`AdicCompletion.completion_tensor_localMaps_surjective`, with its existing
signature and docstring unchanged. The proof explicitly constructs the canonical
maps from `B = R_p tensor_R S` to each `S_q`, then constructs their extensions to
completions by compatible quotient maps. It factors the given map through this
local product map and the existing `completionFiniteExtensionTensorMap`.
Completion-coordinate extensionality and tensor induction prove the factorization;
surjectivity follows by lifting through the two maps.

The new module `Sheaf.RingTheory.CompletionLocalizedAlgebraProductSurjective`
isolates the inverse-limit interpolation part (original steps 1--3). The completed
tensor comparison uses the existing
`AdicCompletion.completion_finite_extension_tensor_bijective`. Its required
quotient-coordinate formula is proved directly by unfolding the constructed map,
not assumed as another hole. The earlier sandbox's unfinished
`CompletionFiniteExtensionTensorMapEval.lean` is not part of this delivery.

No existing public signature or definition changed. The only new definition,
the private `completionMap`, is a real construction from quotient maps and has
no sorry. The interpolation module includes the imports for its stated proof plan.
Node copies record the actual reduction.

## Proved and sorry left

Closed original hole:
`AdicCompletion.completion_tensor_localMaps_surjective`
(node `lem-weil-pbc-completion-tensor-local-maps-surjective`).
Its proof contains no sorry.

Added hole:
`AdicCompletion.completion_localizedAlgebra_product_surjective`
(node `lem-weil-pbc-completion-localized-algebra-product-surjective`), in the new
module. Its entire proof is `:= by sorry`, with a sourced complete proof in words.
It concerns only the completion of the localized algebra and inverse-limit
interpolation, without a completed tensor source. The original theorem combines
this part with the existing tensor comparison by a complete Lean proof.
This is a decomposition: one upper hole closed and one lower hole added, net zero
newly discharged mathematical obligations.

The existing dependency
`AdicCompletion.completion_finite_extension_tensor_bijective` still has sorry in
its own module; this delivery does not modify it. No other hole is added by this
delivery. The previous sandbox's separate evaluation-formula hole was removed;
the formula is now proved in the original theorem.

## No longer needed

Removed direct proof imports from the item's module:
`Sheaf.RingTheory.FiniteAfterCompletion` and
`Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`. Their nodes,
`lem-weil-pbc-finite-after-completion` and
`lem-weil-pbc-localization-prime-residue-field-iso`, remain necessary in the new
interpolation node, whose module imports them. They are moved dependencies,
not globally pruned obligations.

The provisional `Sheaf.RingTheory.CompletionFiniteExtensionTensorMapEval` import
and module are unnecessary: the formula is proved in place. This was an unlanded
sandbox file with no node on the base, so no existing DAG node is pruned.

Every old direct proof dependency removed from the item is accounted for:

- Moved into the interpolation node: `lem-weil-pbc-finite-after-completion`,
  `lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum`,
  `lem-weil-pbc-finite-type-algebra-noetherian`,
  `lem-weil-pbc-localization-at-prime-of-quotient`,
  `lem-weil-pbc-localization-base-change`, `lem-weil-pbc-localization-noetherian`,
  `lem-weil-pbc-localization-prime-residue-field-iso`, and
  `lem-weil-pbc-product-of-localizations-at-maximal`.
- Reached through the tensor comparison node:
  `lem-weil-pbc-completion-finite-module-tensor`.
- `lem-weil-pbc-tensor-cancel-base-change` is no longer a named proof dependency
  of this item or its new reduction. Tensor cancellation is incorporated in the
  existing tensor comparison's proof in words; its DAG does not cite this node.
  This node is a Mathlib leaf, so no Sheaf module is removed by dropping it.

All original quotient-product, localization, Noetherianity, and cofinal-filtration
nodes remain in the interpolation plan. The completion-finite-module-tensor node remains through
`new-completion-finite-extension-tensor-bijective`. No existing node or module is
claimed globally pruned, and no blueprint unit statement or realized step is
bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous attempt was never certified: it reported missing compiled tensor-map
imports, and later acquired an unproved evaluation-formula scratch module with no
node. The compiled tensor dependencies are now available. The evaluation formula
is proved directly and its scratch module is removed from the delivered sources.

Broad simplification in the tensor-induction proof unfolded large completion
constructions and exceeded the single-file time limit. It is replaced by explicit
`map_zero`, `map_add`, and `map_mul` rewrites. The proof uses the actual definition
of the completed tensor map rather than any additional comparison assumption.

The new statement was checked for an empty prime fibre (including `S = 0`),
a field base, and finite algebras with nilpotents. Empty products are the zero
ring and zero is a preimage; the Artinian quotient-product argument accommodates
nilpotents. No nontriviality or domain assumption is added.

The source proof was read in a local Stacks Algebra mirror, at
`lemma-completion-finite-extension` and `lemma-finite-after-completion` (Tags 07N9
and 0394). LeanFinder, Loogle, and Mathlib source searches find ingredients but no
exact local product theorem; the earlier LeanSearch request returned Internal
Server Error. The new node records these searches. No source-level mathematical
error was found.

## New nodes

`lem-weil-pbc-completion-localized-algebra-product-surjective`:
one inverse-limit interpolation theorem in
`lean/Sheaf/RingTheory/CompletionLocalizedAlgebraProductSurjective.lean`.
It carries steps 1--3 of the existing surjectivity node, with the same chapter,
unit, and nearest blueprint ancestor `thm-weil-pbc-finite-etale-lifting`.
It does not contain the tensor-completion comparison, which is supplied by the
existing bijectivity dependency. No change record is needed because no existing
public interface changes.

## Second reading by F2

1. Interface: compared the delivered item with the repository using `diff -u`
   and checked the theorem signature byte for byte. The existing signature,
   docstring, visibility, and public imports are unchanged. The only added
   definition is private. No target, existing definition, or other module is
   adapted; no change record is needed. Verdict: pass.
2. Proof: compiled both delivered modules in import order with `lcompile.py`.
   Neither produced errors or warnings. The item's proof has zero sorry; the new
   module has exactly the one named, documented theorem hole listed above.
   Scratch copies with `#print axioms` show the main theorem and interpolation
   theorem use only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The private `completionMap` and `completionMap_eval` use only the three standard
   axioms. Read the quotient compatibility, tensor coordinate formula, tensor
   induction, and final lifting steps. The map is constructed from quotient maps;
   it selects no arbitrary data from an unproved existence theorem. Verdict: pass.
3. Split statement: read Stacks Algebra `lemma-completion-finite-extension` and
   `lemma-finite-after-completion` in the local source mirror
   `/home/ubuntu/c1-stacks-review/algebra.tex`. The interpolation statement is the
   second equality, without the first equality's completed tensor comparison.
   The S-algebra condition and values on base pure tensors determine each psi;
   the level condition determines g by quotient surjectivity and completion
   extensionality. The proof in words obtains compatible J-adic lifts using
   quotient product isomorphisms, then the identity-induced change of filtration.
   Checked empty Q (including S = 0), a field base, and nonreduced finite algebras:
   n = 0 is the zero quotient; Artinian local factors retain their nilpotents;
   cofinal powers account for unequal J-adic and maximal-ideal-adic filtrations.
   Independent LeanFinder search for semilocal completion products, Loogle search
   for `AdicCompletion, Ideal.map`, and Mathlib grep for semilocal/completion
   equivalences found ingredients, not this statement. Also searched `lean/` and
   the upstream sources present here; product theorems above this item depend on
   it and cannot be used as a shortcut. This is a true, strictly smaller part of
   the argument, not a renamed restatement. Its formal proof remains substantial,
   so it was not closed during this reading. Verdict: pass as decomposition.
4. Route and pruning: read from the surjectivity goal down through g and t. The
   proof uses the existing tensor comparison and proves its evaluation formula
   directly. No shorter applicable theorem was found. Public imports serve the
   unchanged signatures; additional imports are private proof imports. Imports
   in the new holed module supply its stated proof plan. Checked
   `dag/units/sk-thm-p1.json` realized statement and every realized step; none is
   replaced or bypassed. No global module pruning is claimed. Expanded the
   dependency accounting above to name all ten old direct proof dependencies.
   Corrected the first report's claim that the tensor comparison DAG still cites
   `lem-weil-pbc-tensor-cancel-base-change`: it does not. Verdict: pass.
5. Metadata: compared the existing node JSON; only `proof`, `proof_deps`, and
   `proof_origin` change. Each node's proof_deps equals the union of its proof
   steps' uses. The existing node describes the actual constructed g, application
   of interpolation, proved factorization, and lifting through t. The new node
   has a matching verbatim Lean signature, chapter/unit, source, blueprint ancestry,
   creation/Lean records, and recorded Mathlib searches. Verdict: pass.

Second reading changed only this report (complete old-dependency accounting,
correction of the claimed tensor-cancellation DAG edge, and this review) and the new node's search metadata (independent searches appended).
No Lean proof, signature, definition, or import was changed. One upper hole is
closed, one lower hole is added: decomposition, net zero holes discharged.
