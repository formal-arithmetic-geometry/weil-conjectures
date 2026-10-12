## What changed

Added the split-off conormal dimension decomposition theorem
`Algebra.fibre_finrank_eq_cotangent_finrank_add_fin_fun`. The target theorem is
now proved from it and the standard finite function-space finrank formula.

## Proved and sorry left

`Algebra.fibre_finrank_eq_cotangent_finrank_add` is proved. The new strict
intermediate theorem `Algebra.fibre_finrank_eq_cotangent_finrank_add_fin_fun`
remains `sorry`, recording the conormal exact-sequence and separating-basis
argument.

## No longer needed

No imports were removed. The target's original planned dependencies are
represented by the new intermediate theorem rather than used directly in the
target proof.

## Where the brief, the DAG or earlier work was wrong

The full conormal argument is too large for this item, so it is isolated as a
strict intermediate theorem whose extra summand is the explicit function space
`Fin r → q.ResidueField`; the target then closes by Mathlib's finrank formula.

## New nodes

`lem-weil-pbc-regular-local-fibre-finrank-add-fin-fun`.

## Second reading by C1

1. I compared the delivered module and target node with the repository versions.
   The target theorem signature and all existing declarations are unchanged; the
   only added declaration is the named split-off intermediate theorem.
2. I compiled the module with `lcompile.py`. It has no errors, forbidden commands,
   or hollow definitions. The sole remaining `sorry` is
   `Algebra.fibre_finrank_eq_cotangent_finrank_add_fin_fun`, and it has a matching
   split node and proof description.
3. The split-off statement is a strict decomposition with the explicit
   `Fin r → q.ResidueField` summand; the target reduces it using
   `Module.finrank_fintype_fun_eq_card` and `Fintype.card_fin`.
4. The target proof follows the split node and then the standard finite
   function-space finrank formula; the DAG target proof and `proof_deps` agree
   with the Lean proof. The unit route is retained through the split node.
5. Imports and declarations were checked for visibility and source order; the
   new theorem's docstring records the conormal and separating-basis source.

I changed the accidental ordinary comment before the original theorem back to a
docstring and added this second-reading record. No mathematical statement or
proof was changed.
