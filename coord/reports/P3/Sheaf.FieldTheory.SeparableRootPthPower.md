## What changed

Proved `Polynomial.exists_pow_eq_of_distinct_roots_coeff_pow` in
`lean/Sheaf/FieldTheory/SeparableRootPthPower.lean`, preserving its signature,
visibility, public imports, and existing docstring. Added the proof-only import
`Mathlib.FieldTheory.KummerPolynomial` for the existing irreducibility leaf.
Updated the item's DAG proof to match the Lean argument.

Distinct roots give separability using root multiplicities. The proved Mathlib
polynomial-range characterization constructs the coefficient-root polynomial Q
over L; separability reflects through Frobenius. A p-th root gamma of alpha in
an algebraic closure is a root of Q and is therefore separable over L. If alpha
had no p-th root in L, gamma's minimal polynomial would be the irreducible
X^p - alpha, whose derivative vanishes, contradicting separability.

The source is Stacks Fields, Tag 031V (2), with Tag 09HF. Its text was read in
`/home/ubuntu/work-bp/sheaf/literature/stacks-project/fields.tex` because the
literature source is not materialized in this clone. The unit `sk-thm-p1`
statement and realized steps are untouched.

## Proved and sorry left

Closed one hole: `Polynomial.exists_pow_eq_of_distinct_roots_coeff_pow`
(node `lem-weil-pbc-separable-root-pth-power`). No sorries remain in the item;
no holes, statements, definitions, or modules were added elsewhere.
This is a proof, not a decomposition: it uses only proved Mathlib declarations.
The final module compiles cleanly through `lcompile.py`.

## No longer needed

None of the original imports or DAG dependency nodes are removed. All six
original proof dependency nodes still describe notions or the irreducibility
lemma used by the final proof. No Sheaf or WeilConjectures proof modules are
needed. The explicit Bezout transport, repeated-root transport through
Frobenius, and factorization `(X - gamma)^p` calculations are replaced by
Mathlib's separability-map and minimal-polynomial interfaces.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. As the existing node already notes, the assumed
separability of L/E is not needed; the signature keeps it unchanged. The old
DAG chose Q over E, whereas this implementation constructs Q directly over L
by mapping the supplied coefficient roots into L. No definition or interface
was changed and no forced adaptations are needed.

## Second reading by P3

1. **Interface — PASS.** Compared the only delivered module with the repository
   using `diff -u`. The existing theorem signature, visibility, docstring and
   public imports are byte-for-byte unchanged. Only its proof and the private
   KummerPolynomial import were added. No definitions, statements, change
   records or adapted modules were introduced.
2. **Proof — PASS.** Independently compiled the delivered file through
   `lcompile.py` with no errors or warnings. A scratch copy with
   `#print axioms Polynomial.exists_pow_eq_of_distinct_roots_coeff_pow`
   reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
   The delivered file has no sorry or forbidden declarations. Both Q and gamma
   are obtained from proved Mathlib existence theorems; no unproved witness
   provides data. Read the Frobenius evaluation identity and minimal-polynomial
   contradiction in full: they establish precisely the original conclusion.
3. **Split statements — PASS (none).** No new statements or holes were split
   off. Checked the edge cases: alpha = 0 is already a p-th power; constant
   nonzero P cannot satisfy hroot; zero P is excluded; p = 2 is covered by the
   derivative-zero argument; the prime hypothesis excludes p = 0 and p = 1.
4. **Route and pruning — PASS.** Read the source proof of Fields 031V(2) in
   the local literature mirror and the existing 09HF Mathlib leaf. Independently
   searched the local Mathlib separability/purely-inseparable files and both
   library roots for coefficient-power, Frobenius and separable-root results.
   No direct replacement for this theorem was found. The proved Mathlib
   range, separability-map and minimal-polynomial interfaces already shorten
   the source argument; no rewrite is warranted. Each import supplies a
   signature notion or a used proof lemma, and the added proof import is
   private. All six original proof dependencies remain used, so the
   `No longer needed` section is complete. The unit sk-thm-p1 and its realized
   statement and steps are unchanged; this proof only shortens a lower node.
5. **DAG — PASS.** Compared the node JSONs: only proof and proof_origin differ.
   Matched each step to the Lean proof and checked each dependency's recorded
   Mathlib declaration. proof_deps equals the union of the steps' uses and
   matches the unchanged original dependency set. No new nodes are needed.

Second reading changed only this report, adding the independent review and
validation evidence. The Lean proof and node require no repairs. Closed holes:
`Polynomial.exists_pow_eq_of_distinct_roots_coeff_pow` (one of one); added holes:
none. This is a completed proof, not a decomposition.
