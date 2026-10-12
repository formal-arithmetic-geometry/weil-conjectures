## What changed

Proved `Polynomial.exists_monic_aeval_eq_zero_map_eq_of_isIdempotentElem_quotient` in
`Sheaf.RingTheory.IntegralIdempotentAnnihilatingPolynomial` using Mathlib's Stacks 00H5
lemma and polynomial composition. Multiplication of the monic equation by `X` ensures
that the exponent is positive. The zero base ring is handled separately. Updated the
existing node's proof and proof origin to match this construction. Statements are unchanged. The second reading makes the ideal-integrality import
private and publicly imports only the modules needed for the statement. Local launcher compilation passes without warnings.

## Proved and sorry left

Closed the sole hole:
`Polynomial.exists_monic_aeval_eq_zero_map_eq_of_isIdempotentElem_quotient`
(node `lem-weil-pbc-integral-idempotent-annihilating-polynomial`).
No sorry remains in the item. No holes added; no decomposition.

## No longer needed

None. The existing proof dependency
`lem-weil-pbc-integral-extended-ideal-element-monic` is used directly through its Mathlib
match `Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map`. The original public import of
`Mathlib.RingTheory.IntegralClosure.Algebra.Ideal` is now a private proof import.
Its public role is replaced by `Mathlib.RingTheory.IntegralClosure.Algebra.Defs`,
`Mathlib.Algebra.Polynomial.AlgebraMap`, and `Mathlib.RingTheory.Ideal.Maps`,
which supply `Algebra.IsIntegral`, `aeval`, and `Ideal.map` for the statement.
The quotient definitions and idempotent imports remain public for the statement.
No proof-dependency node or module is pruned. No Sheaf or WeilConjectures proof
modules are needed; none was imported originally. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement found. The degree-zero case in the planned proof can be avoided
by multiplying every obtained equation by `X`; this gives exponent `g.natDegree + 1`.
The local repository lacks the cited Stacks source, so the proof was checked against the
existing local copy at `/home/ubuntu/c1-stacks-review/more-algebra.tex`,
`lemma-helper-integral`, lines 1960–1975. Edge cases covered by the Lean proof include
zero A, zero B, I equal to top, and an original monic equation of degree zero.


## Second reading by C1

1. PASS: Compared the sole delivered module against the repository with `diff`.
   The existing theorem signature is byte for byte unchanged. There are no definitions,
   new declarations, or statement changes. The import-visibility change has the
   change record listed below (required by the preflight).
2. PASS: Compiled the module locally through `lcompile.py` without warnings.
   A scratch copy with `#print axioms` reports only `propext`, `Classical.choice`,
   and `Quot.sound`. No sorry or forbidden declaration occurs in the delivered module.
   The existential polynomial in the proof comes from a proved Mathlib theorem;
   no data is chosen from an unproved existence statement.
3. PASS: No statement is split off and no hole is added. Checked the mathematical
   argument for zero A (which forces zero B), zero B with nonzero A, the top ideal,
   and degree-zero g. Multiplying by X gives a positive exponent in every case.
   Repeated LeanFinder and Loogle searches using different wording and searched
   Mathlib, upstream WeilConjectures, and lean/Sheaf by annihilator/idempotent words
   and source tag: no direct existing theorem for the item was found.
4. PASS after import repair: The proof uses the existing Mathlib match of
   `lem-weil-pbc-integral-extended-ideal-element-monic` and elementary composition;
   no new helper is needed. Checked `dag/units/sk-thm-p1.json` and its `realized`
   statement and steps: this auxiliary node is below those steps, none is bypassed.
   The old proof dependency is still used, so the pruning list is complete (none).
   Made the proof-only ideal-integrality import private, with explicit public
   imports for the signature's integral algebra, polynomial evaluation, and ideal map.
5. PASS: The node changes only proof and proof_origin; proof_deps keeps exactly
   the Mathlib ingredient used by the Lean proof. The updated steps describe
   h = X*g, d = natDegree g + 1, composition with X*(X-1), and the zero-ring case.
   There are no new nodes to validate.

Changes by the second reader: repaired import visibility and updated the theorem's
proof docstring to match the uniform multiplication by X and the zero-base-ring case.
The Lean proof itself is unchanged. Closed one original hole and added zero holes.


Import change record: `coord/changes/integral-idempotent-annihilator-proof-import.md`.
The first dry run requested this record for the public import removal; added it
with the full downstream list. The sole direct importer, `LiftIdempotentUpstairs`,
was compiled in a scratch set against the revised item, without warnings.
