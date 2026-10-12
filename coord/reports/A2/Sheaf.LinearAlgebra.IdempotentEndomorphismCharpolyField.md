## What changed

Proved `LinearMap.charpoly_toMatrix_of_idempotent` without changing its signature.
The proof uses Mathlib's explicit conjugacy of an idempotent to the product of the
identity on its range and zero on its kernel, characteristic-polynomial conjugacy
and product formulas, rank-nullity, and divisibility of powers. Replaced the proof
import of `Sheaf.LinearAlgebra.IdempotentImageBaseChange` with Mathlib projection
and finite-dimensional linear-algebra imports. Updated the node's proof route and
proof dependencies to agree with the Lean proof. The unit's realized statements
and proof steps are unaffected.

## Proved and sorry left

Closed the one existing hole: `LinearMap.charpoly_toMatrix_of_idempotent`
(node `lem-weil-pbc-idempotent-endomorphism-charpoly-field`).
No holes added, no `sorry` left, and no new declarations. This is a complete proof,
not a decomposition. The proof works for n = 0 and for the zero and identity maps;
it uses neither positive dimension nor any characteristic assumption.

## No longer needed

Removed import `Sheaf.LinearAlgebra.IdempotentImageBaseChange` and proof dependency
`lem-weil-pbc-idempotent-endomorphism-image-base-change`: the finite projectivity
and base-change claims are unnecessary for this field-only calculation. Mathlib
already supplies the complementary range/kernel decomposition and its conjugacy.
All five remaining proof-dependency nodes are used through their recorded Mathlib
matches: rank-nullity, basis/conjugacy invariance, product charpoly, identity
charpoly, and zero charpoly. No other nodes or modules are pruned by this proof.

## Where the brief, the DAG or earlier work was wrong

No statement errors found. The original plan depended on a much stronger
image/base-change theorem than needed. The second reader updated the declaration docstring to describe Mathlib's
projection theorem, matching the updated DAG and proof. No definitions, public imports, or target statements changed.


## Second reading by A2

1. Compared the only delivered module and its node against the repository with
   `diff -u`. The full theorem signature is byte-for-byte unchanged (also checked
   programmatically): arbitrary universe, field, natural number including zero,
   idempotent endomorphism of `Fin n → k`, arbitrary basis, range finrank, the
   exact characteristic-polynomial equality and divisibility. No definitions or
   public imports changed; no change record is needed. Verdict: pass.
2. Compiled the module with `lcompile.py`, without errors or warnings. Compiled a
   scratch copy with `#print axioms LinearMap.charpoly_toMatrix_of_idempotent`:
   exactly `propext`, `Classical.choice`, and `Quot.sound`. Scanned for forbidden
   declarations/attributes and sorries; none occur. No data is chosen from an
   unproved existence statement. Verdict: complete proof, one hole closed.
3. No split-off statements, new declarations, new nodes, or holes were added.
   Independently searched Mathlib via `msearch.py ... grep` for charpoly with
   IsProj/idempotence, and searched the upstream linear-algebra directories and
   local `lean/Sheaf`/`lean/WeilConjectures` for projection/idempotent charpoly
   routes. No shorter matching theorem was found. The zero-dimensional case
   gives 1; p = 0 gives X^n; p = 1 gives (X - 1)^n. Each divides the stated
   product, and the argument works in every field characteristic. Verdict: pass.
4. Read Mathlib's projection conjugacy and the five retained dependency nodes'
   Mathlib matches. Rank-nullity gives the kernel exponent and r ≤ n; conjugacy
   invariance and prodMap reduce the polynomial to charpoly_one/charpoly_zero;
   pow_dvd_pow and mul_dvd_mul prove divisibility. No remaining Sheaf hole is
   used. The public ToMatrix import supplies the signature; the plain Projection
   import supplies the conjugacy; removing FiniteDimensional.Lemmas in a scratch
   copy failed because finrank_range_add_finrank_ker was unavailable, so retained
   it. The report lists the sole removed old proof dependency and its module.
   Read `dag/units/sk-thm-p1.json`: neither this item nor the removed dependency
   realizes a unit statement or step; the unit's realized route stays intact.
   Verdict: pass, pruning below unit level only.
5. Checked the node's four proof steps against the Lean proof and all five
   Mathlib matches. Its proof_deps is exactly the union of the steps' uses;
   proof_origin records the implemented route. Only proof, proof_deps, and
   proof_origin differ from the repository node. No node statement or Lean
   statement metadata changed. Verdict: pass.

Changed only the stale theorem docstring, replacing its citation of the removed
image/base-change dependency with Mathlib's explicit projection conjugacy. The
proof itself was correct and is retained unchanged. All existing and added
holes are accounted for in `## Proved and sorry left` above.
