## What changed

Proved `FieldExtension.exists_coefficientRoot_extension` with its original signature and
visibility unchanged. Its sole added import, `Sheaf.FieldTheory.FiniteRootedExtension`, is
proof-only. Two proved private helpers extract the finite constant set by induction on the
intermediate-field adjoin and on the finite set of polynomial coefficients. They handle sums,
products and inverses directly, avoiding multivariate polynomial denominator bookkeeping.

Added the fully proved module `Sheaf.FieldTheory.FiniteRootedExtension`, containing
`FieldExtension.exists_finiteRooted_extension`. It constructs actual intermediate fields in
`AlgebraicClosure K`, with the constant and variable root equations explicit in its conclusion.
Finiteness, pure inseparability, algebraic independence, the embedding and compositum equality
are all proved from Mathlib. Its three proof-only Mathlib imports are used for the algebraic
closure, the adjoin criterion for pure inseparability and algebraic independence after algebraic
extension of constants. No definition or existing public interface changes; no adaptations.

A declaration-local unused-variable linter option surrounds the original theorem because its
unchanged existential instance binders are named but referenced only implicitly. The new
helper uses underscore-prefixed names for those binders. Both files compile without warnings.
Updated the original node's proof and proof dependencies to the implemented argument.

## Proved and sorry left

Closed the one original hole, `FieldExtension.exists_coefficientRoot_extension`, node
`lem-weil-pbc-coefficient-root-extension`. Added zero holes. The new theorem
`FieldExtension.exists_finiteRooted_extension`, node `lem-weil-pbc-finite-rooted-extension`,
is also fully proved. Both private helpers are fully proved. There are no remaining `sorry`s
in either delivered module, and no unproved existence theorem supplies their data.

The coefficient calculation is valid even with an empty tuple and a nonperfect base field:
the finite constants actually acquire roots in l. The zero polynomial needs no nonzero
coefficients; coefficients outside the support use the root zero. The field construction
works for empty C, empty s, or both: the finite images and adjoin inductions include these
cases, and independence of the empty tuple needs no exceptional assumption.

## No longer needed

No existing import was removed and no module or node is globally pruned. All seven original
proof dependencies remain used in the delivery: `def-pc-field-extension`,
`def-weil-algebraic-closure`, `def-weil-algebraic-element`,
`def-weil-pbc-finite-purely-inseparable-extension`, `def-weil-pbc-transcendence-basis`,
`def-weil-ring-frobenius`, and `lem-weil-pbc-algebraic-generators-finite-extension`.
The algebraic-closure, algebraic-element and finite-generators dependencies move from the
original node's immediate proof dependencies to the new, fully proved construction node;
this is not pruning. The original proof's explicit quotient presentations, numerator
polynomials h and multivariate coefficient expansion are unnecessary: adjoin induction
proves the finite constant criterion directly. The original module had no proof imports
for those calculations, so no removed module is claimed.

## Where the brief, the DAG or earlier work was wrong

The rejected split did not require roots of constants or variables and did not constrain
its ambient field to the compositum. Its properties assertion was false. That proposal
has been replaced entirely, including its obsolete report and second-reading text.
The delivered construction states the constant and variable root equations and proves
its compositum equality; no analogous unsupported implication remains.

The original plan is mathematically valid. It can be shortened by extracting constants
through the field operations rather than explicit rational expressions. Algebraic
independence uses Mathlib's `AlgebraicIndependent.extendScalars` for the finite algebraic
constant extension, followed by `AlgebraicIndependent.of_ringHom_of_comp_eq` for Frobenius.
The unit record `dag/units/sk-thm-p1.json` and all its realized statements and steps stay
unchanged. No unit route is bypassed.

The local `literature/stacks-project/algebra.tex` file is absent. Read the primary source
at https://stacks.math.columbia.edu/tag/04KM, specifically its coefficient-root construction
and compositum paragraph. That source omits construction details; the delivered proofs
supply them, and their proof_origin records explicitly identify the agent-written details.
LeanSearch returned Internal Server Error, recorded as unavailable. LeanFinder, Loogle,
Mathlib/source searches and blueprint searches were run; no exact packaged construction
was found. `blueprint_refs.py ancestor` does not follow the original node's module-valued
created.item, so the new node inherits its recorded blueprint ancestor and prepends the
original node to its via list instead.

## New nodes

`lem-weil-pbc-finite-rooted-extension`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-rooted-extension.json`, records the
fully proved finite root construction in `lean/Sheaf/FieldTheory/FiniteRootedExtension.lean`.
Its statement does not mention P; its proof constructs the finite fields and provides the
explicit root equations needed by the independent coefficient calculation. Its Lean
statement is the verbatim theorem signature, its searches record the actual tool results,
and its proof dependencies are the union of its proof steps. No change records are needed.

## Second reading by A3

1. **Visible changes.** I compared both delivered modules and the changed coefficient-root
node with the repository versions. The existing theorem signature is byte-for-byte unchanged;
the only interface addition is the separately recorded new construction module and node.
No undeclared statement or definition change is present.

2. **Proof validity.** Both modules compile with `lcompile.py --all`; searching the delivered
files finds no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or `sorryAx`.
The construction uses actual algebraic-closure subfields, so no definition receives arbitrary
data from an unproved existence claim. Its declarations have only the permitted foundational
axioms; delivery preflight performs the axiom check.

3. **Statements and nodes.** The new finite-rooted statement is a strict auxiliary result:
it supplies finite purely inseparable fields, rooted constants and variables, independence,
and the compositum equality used by the target. It is neither a restatement of the target nor
available under another name in the repository. Its docstring, node statement, proof steps,
dependencies, and proof origin agree with the Lean declaration.

4. **Pruning and route.** The proof follows the unit route through the finite rooted extension
node and retains every dependency used by the implementation. The only added import is proof-only
and all existing imports remain necessary; consequently there are no omitted pruning entries.
The finite-constant induction is shorter than the former explicit quotient-polynomial route.

5. **Unit preservation.** `dag/units/sk-thm-p1.json` remains unchanged, including its realized
statement and steps. The coefficient-root target is proved using that unit's finite-rooted
construction, with no bypass of the chapter route.

I changed only this report section after reading: no Lean source, statement, definition, node,
or import required repair.
