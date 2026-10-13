## What changed

Proved `KaehlerDifferential.exists_basis_differentials_of_pBasis` with its original
signature and visibility. The proof first shows that the universal derivation kills
B = kK^p, then uses the monomial basis to prove that the dt_i span. Evaluation of
polynomials is surjective by the same basis expansion. Descended partial derivatives
give dual linear forms, proving independence; `Module.Basis.mk` supplies the basis.

Added `Sheaf.FieldTheory.PIndependentEvaluationKernel` and its fully proved theorem
`MvPolynomial.aeval_pderiv_eq_zero_of_pIndependent`. It assumes only independence
of bounded monomials, and proves stability of the polynomial evaluation kernel.
Its proof reduces exponents modulo p in the quotient by the p-power relations,
proves quotient evaluation injective, and applies Leibniz to the relation ideal.
Updated both DAG proof records to follow the compiled proofs. No existing definition,
statement, signature, or visibility changed. No other module was adapted.

Both modules compile cleanly through `lcompile.py --all`, with no warnings.
The helper takes about 19 seconds and the original module about 3 seconds.

## Proved and sorry left

Closed the original hole:
`KaehlerDifferential.exists_basis_differentials_of_pBasis`
(node `lem-weil-pbc-p-basis-differentials-basis`).

The new theorem `MvPolynomial.aeval_pderiv_eq_zero_of_pIndependent`
(node `lem-weil-pbc-p-independent-evaluation-kernel`) is fully proved too.
One original hole closed, zero holes added, zero sorries left anywhere in the delivery.
No decomposition into unproved statements remains.

## No longer needed

No import was removed relative to the original file: its three public imports are
needed by its unchanged statement. The proof imports the new kernel-stability module. Second reading removed the
redundant proof imports Mathlib.LinearAlgebra.Basis.Basic and
Mathlib.LinearAlgebra.LinearIndependent.Lemmas from the original module, and
Mathlib.LinearAlgebra.Finsupp.LinearCombination from the new helper module.
Their declarations are already available through the retained imports.

The proof no longer needs these original DAG dependencies:
- `lem-weil-pbc-polynomial-ring-kahler-basis-any-variables`;
- `lem-weil-pbc-jacobi-zariski-differential-maps`;
- `lem-weil-pbc-kahler-differentials-first-exact-sequence`.

In particular `Mathlib.RingTheory.Kaehler.Polynomial` is not imported. The two
exact-sequence declarations are in `Mathlib.RingTheory.Kaehler.Basic`, which remains
necessary for the statement and universal property; that module itself is not pruned.
No Sheaf dependency module is removed. The binding statements and steps in
`dag/units/sk-thm-p1.json` are unchanged; this is a simplification strictly below them.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG's quotient presentation argument works,
but the two exact sequences can be avoided by constructing the dual derivations.
The new algebra lemma needs independence only, not spanning of K. The source was
read at [Stacks Tag 07P2](https://stacks.math.columbia.edu/tag/07P2), in particular
the presentation in the proof of (a) implies (b). The local literature directory
contains citation lists rather than the Stacks TeX file.

LeanSearch returned HTTP 500 and is recorded as unavailable, not as a negative
search. LeanFinder, Loogle and the recorded grep searches found no matching result.
Blueprint searches for p-basis, kernel derivative, and evaluation kernel found no
duplicate of the new theorem. Existing partial-derivative and polynomial nodes
are cited instead of duplicating those notions.

## New nodes

`lem-weil-pbc-p-independent-evaluation-kernel` records the fully proved theorem
in `lean/Sheaf/FieldTheory/PIndependentEvaluationKernel.lean`. It is strictly the
polynomial-kernel part of the argument and does not mention Kähler differentials
or assert the existence of any basis. Edge cases checked: empty I is vacuous;
infinite I uses finite supports; no perfection assumption on k is used; spanning
of K is not assumed. Each coefficient t_j^p belongs to the concrete intermediate
field by `IntermediateField.subset_adjoin`. No change record is needed.


## Second reading by R1

1. Compared the full original-module diff with the repository: the existing theorem
   signature, universes, visibility and three public imports are byte for byte unchanged.
   Only the proof, its explanatory docstring, and private proof imports changed. There
   are no changed definitions, target statements, or forced adaptations. No change
   record is needed. Verdict: pass.
2. Read both proofs and compiled both modules locally in import order, without errors
   or warnings. Scratch copies with `#print axioms` showed exactly `propext`,
   `Classical.choice`, and `Quot.sound` for both theorems. No sorry or forbidden
   declaration occurs in the delivery. The concrete quotient and coefficients are
   constructed directly; there is no data chosen from an unproved existence theorem.
   Verdict: pass.
3. There are no split-off unproved statements. The proved new helper is strictly the
   evaluation-kernel part of the argument, not a restatement of the basis theorem.
   Read Stacks Tag 07P2, specifically its presentation in (a) implies (b), and checked
   the exponent-reduction, quotient-injectivity and ideal-derivative argument against
   the code. Empty I gives no derivative to check; infinite I uses finite supports;
   p prime supplies p > 0 for remainders; no spanning or perfection is used in the
   helper. Fresh LeanFinder search for formal differentiation descending to a field
   generated by p-independent elements, Loogle search `MvPolynomial.pderiv,
   LinearIndependent`, and grep for p-basis and derivative kernels found no replacement.
   Also searched the repository and upstream field/ring-theory files: the related
   p-independent differential theorem depends on this item and cannot shorten it.
   Verdict: pass.
4. The main proof first kills kK^p and proves spanning directly; kernel stability
   descends partial derivations whose universal lifts are dual to dt_i. This avoids
   the polynomial differential basis and both exact sequences. The three old unused
   proof dependencies are all listed above. Read `dag/units/sk-thm-p1.json` realized:
   this item is below its binding statements and steps, none of which is bypassed.
   Tested removing proof imports in scratch copies: three were redundant and removed;
   removing Ideal.Quotient.Operations failed, so it remains. Verdict: pass after pruning.
5. Read both node records against their Lean proofs: proof steps, their union of uses
   in proof_deps, and proof_origin agree. The new node has its source, searches,
   creation metadata, blueprint ancestry, chapter, unit, and Lean attachment. Corrected
   its recorded Lean statement to the exact declaration text: its bound index was
   recorded as i where the file uses j. This is metadata only. Verdict: pass after repair.

Second reading changed only redundant proof imports and the new node's verbatim
Lean statement record; neither theorem's statement or proof body changed. One
original hole closed, no holes added, no unproved split-off statements.
