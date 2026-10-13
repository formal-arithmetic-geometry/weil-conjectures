## What changed

The unchanged theorem `IntermediateField.finiteDimensional_finrank_adjoin_pth_roots`
now has a genuine induction proof. It restricts the independent family to the first n
indices, obtains nonmembership of the final root, proves irreducibility of
`X ^ p - C b` using Mathlib, identifies the minimal polynomial, applies the simple
adjunction finiteness and finrank results, and multiplies degrees. A proved range-union
identity and `IntermediateField.adjoin_adjoin_left` identify the final field.

Added `Sheaf.FieldTheory.PthRootNotMemPreviousAdjoin`, containing only the smaller
nonmembership obstruction, with a complete source proof in its docstring. Removed the
first worker's `PthRootsMonomialBasis` module and node: that stronger statement included
both target conclusions unchanged and its proof dependency was circular.

The original public imports, visibility, universes and target signature are unchanged.
The only added proof imports are `Mathlib.Algebra.CharP.Algebra` (transfer of characteristic)
and `Sheaf.FieldTheory.PthRootNotMemPreviousAdjoin`. Explicit imports of Adjoin.Basic,
KummerPolynomial and Minpoly.IsIntegrallyClosed were unnecessary; the required adjunction,
irreducibility and minimal-polynomial results are already available through original imports.
No definitions or existing intermediate statements were changed.

## Proved and sorry left

Hole closed: `IntermediateField.finiteDimensional_finrank_adjoin_pth_roots`
(node `lem-weil-pbc-pth-roots-extension-degree`), the only original hole in the item.

Hole added: `IntermediateField.pth_root_not_mem_previous_adjoin`
(node `lem-weil-pbc-pth-root-not-mem-previous-adjoin`). Its conclusion is just that the last
root does not belong to the preceding generated field. It supplies neither a basis,
finite dimensionality nor any degree formula. This is a strictly smaller part of the
source argument, unlike the rejected monomial-basis restatement.

This delivery is a decomposition: one original hole closed, one smaller hole added,
net zero holes closed. The target's proof still depends transitively on the named open
lemma. Both declarations' axiom checks report only `propext`, `Classical.choice`,
`Quot.sound` and `sorryAx`. There are no other holes, data definitions, or chosen witnesses
from an unproved existence theorem.

## No longer needed

No repository import is removed and no existing library module is pruned.
The undelivered `Sheaf.FieldTheory.PthRootsMonomialBasis` and
`lem-weil-pbc-pth-roots-monomial-basis` are removed from the sandbox.

Every old direct proof dependency absent from the revised target node is accounted for:

- `def-weil-algebraic-closure`: root existence is supplied by the unchanged `hα` hypothesis;
  the algebraic-closure assumption and its public import remain in the signature.
- `def-weil-algebraic-element`: the proof constructs an explicit monic annihilating
  polynomial and uses `IsIntegral`, without a separate appeal to `IsAlgebraic`.
- `lem-weil-pbc-finite-dimensional-domain-is-field`: retained transitively in the
  nonmembership lemma's monomial-span argument, rather than used directly by the target.
- `def-weil-pbc-kahler-differentials`: likewise retained in the nonmembership lemma;
  the differential-independence hypothesis and its public import remain unchanged.

The field-extension, polynomial, simple-power-basis and degree-multiplicativity nodes
remain. The existing Mathlib leaf `lem-weil-pbc-x-pow-p-minus-t-irreducible` is now named
explicitly, matching `X_pow_sub_C_irreducible_of_prime` in the Lean proof.

## Where the brief, the DAG or earlier work was wrong

The first worker replaced the target by one application of a new theorem containing
both target conclusions plus a basis. This moved the entire hole and was not a valid
split. Its new node also depended on the target itself, creating a circular plan, while
the target's existing DAG proof had not been updated. Its docstring had an overlong line.
The second reading repaired all these faults; no statement correction is needed.

The source is Stacks Project Tag 07DZ (Lemma 10.158.3), read directly at
https://stacks.math.columbia.edu/tag/07DZ because the literature source is absent on this
machine. The nonmembership argument is precisely its displayed Frobenius computation.
The new lemma includes the justification that bounded monomials span the preceding
field, and does not assume their independence or the target's degree formula.

## New nodes

`lem-weil-pbc-pth-root-not-mem-previous-adjoin`, in
`lean/Sheaf/FieldTheory/PthRootNotMemPreviousAdjoin.lean`, isolates original plan steps 2
and 3: the bounded monomial span is a finite-dimensional domain and hence a field;
Frobenius followed by the universal derivation contradicts differential independence.
Its source, full proof, searches, verbatim Lean signature, creation and blueprint lineage
are recorded. No change records are required: no existing interface changed.

## Second reading by A3

1. Compared the delivered target module with the repository using `diff`. The existing
   theorem signature is byte for byte identical, including all characteristic, algebra,
   closure, independence and root-equation hypotheses and the conjunction of finiteness
   and exact finrank. Public imports and visibility are identical. Only its proof,
   proof docstring and two private imports changed. Verdict: no accidental interface change.
2. Compiled both modules in import order with `lcompile.py`, without errors or warnings.
   The target contains no direct hole; the only hole is the new named nonmembership
   theorem. Scratch copies with `#print axioms` for each declaration show exactly the
   allowed three axioms and the expected transitive `sorryAx`. Scanned the Lean for
   forbidden declarations and for holes in data: none. Verdict: valid conditional proof.
3. Read Tag 07DZ and checked the new lemma's hypotheses and all steps. The finite monomial
   span is closed under products by reducing exponents using the root equations, is a
   domain inside Omega, and becomes a field by the existing finite-domain lemma. Thus
   expansion in the span uses no unproved basis or degree formula. Frobenius gives an
   equality in k; Leibniz kills p-th power coefficients and produces a relation whose
   last coefficient is 1. Small cases: n=0 reduces to d(beta^p)=0; p=2 still has exponent
   1 available; repeated a_i cannot satisfy independence; over a perfect field every
   such nonempty independent family is impossible. No algebraic closure is needed for
   this lemma. Searched Mathlib with fresh LeanSearch, Loogle, LeanFinder and grep queries,
   and searched both local Lean roots and DAG statements. LeanSearch was unavailable
   (recorded honestly); Loogle's cotangent-disjointness result and LeanFinder's purely
   inseparable exponent results do not state the needed obstruction. Existing
   `PIndependentDifferentialsIndependent` goes in the opposite direction and does not
   supply it. Verdict: true, needed, strictly smaller, not a duplicate.
4. Checked the proof from the target downward. Mathlib supplies irreducibility, the
   monic minimal-polynomial characterization, the simple-extension degree and finiteness,
   and the tower law; only the differential obstruction remains open. Removed redundant
   added Mathlib imports and the invalid stronger split. Listed every unused old direct
   proof dependency above, distinguishing retained transitive uses from pruning.
   Read `dag/units/sk-thm-p1.json`: this item is below the unit's realized nodes; no unit
   statement or realized step is bypassed or changed. Verdict: genuine source induction
   and complete pruning account, with no claimed net proof gain.
5. Updated the original node's proof, proof_deps and proof_origin to match induction,
   nonmembership, irreducibility and tower multiplication. The new node has no dependency
   on the target and its proof_deps is exactly the union of its steps' uses. Its Lean
   record quotes its signature verbatim. No target statement or unit record changed.
   Verdict: DAG and Lean agree; the circular monomial-basis node is gone.

Second reading changed the invalid restatement into an actual induction, added one
strictly smaller source lemma, restored the original file header and documentation,
minimized the proof imports, replaced the circular node and synchronized the target DAG.
