## What changed

Removed the private declaration `integral_pair_factorization_of_lifting`, which duplicated
word-for-word the existing helper statement in `Sheaf.RingTheory.HenselianFactorizationCriterion`.
Its fully proved Bezout argument is now inlined at the point where the target theorem applies
factorization lifting. The public theorem `henselianRing_of_isIntegral`, its signature, and all
public imports are unchanged. The proof adds plain imports of `Sheaf.RingTheory.HenselianFactorizationCriterion` and
`Sheaf.RingTheory.MonicFactorizationOfIdempotent` relative to the repository baseline.
No new declarations or nodes were added.

## Proved and sorry left

Closed: `henselianRing_of_isIntegral` (node
`lem-weil-pbc-integral-over-henselian-pair`). The inlined factorization argument is fully proved.
No `sorry` remains in the delivered module, and no `sorry` was added elsewhere.
Closed one local hole out of one; added zero holes. The axiom probe still reports
`sorryAx` through the imported theorems, so this delivery does not claim an axiom-clean
proof of the entire dependency closure.

## No longer needed

The duplicate private helper declaration is no longer needed. The proof still uses
`Sheaf.RingTheory.HenselianFactorizationCriterion`,
`Sheaf.RingTheory.HenselianIntegralIdempotentLifting`, and
`Sheaf.RingTheory.MonicFactorizationOfIdempotent`; no proof dependency or public import was
removed.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery introduced `integral_pair_factorization_of_lifting` with a proposition already
stated by the private helper `factorization_of_lifting` in
`Sheaf.RingTheory.HenselianFactorizationCriterion`. The landing check correctly rejected the
second declaration. Inlining the argument removes the duplicate while retaining the same proof
route and target statement.

## Second reading by A3

1. **Interfaces unchanged — pass.** Compared the sole delivered Lean module against
   `lean/Sheaf/RingTheory/IntegralOverHenselianPair.lean` with `diff -u`. The only existing
   declaration is `henselianRing_of_isIntegral`; its complete signature, universes `u v`,
   commutative-ring hypotheses, algebra structure, integrality hypothesis and extended-ideal
   conclusion are byte-for-byte unchanged. Both public imports and visibility are unchanged.
   No definitions or other modules are delivered, so there are no forced adaptations.
2. **Proof and axioms — pass.** Compiled the delivered module through `lcompile.py --all`:
   no errors or warnings. A fresh scratch copy of the actual inlined proof, with `#print axioms`,
   checks `henselianRing_of_isIntegral` and its three principal imported theorems. Each probe reports only `propext`, `Classical.choice`, `Quot.sound`, and transitive
   `sorryAx` from the compiled imported theorems. No forbidden commands, new axioms, hollow
   definitions or local `sorry` occur. The explicit Bezout
   computation proves `(b*h₀)^2 - b*h₀ = -(a*b)*(g₀*h₀)`. The two quotient maps kill `JC`,
   so the congruence of the lifted idempotent gives exactly the required residues `1` and `0`.
   All witness choices occur inside a proof of a proposition; none defines arbitrary data.
3. **Split statements — pass, none.** No statements or nodes were added and no holes were
   split off. Re-searched with LeanFinder (integral extension of a henselian pair), Loogle
   (`HenselianRing, Algebra.IsIntegral`: zero hits), and `rg` in the library and Mathlib.
   No shorter public integral-extension theorem was found. The existing private
   `factorization_of_lifting` is inaccessible from this module; inlining its argument avoids
   introducing a duplicate declaration. Read its proof and the public imported theorem
   statements rather than relying on their names.
4. **Route and pruning — pass.** Read Stacks `lemma-integral-over-henselian-pair` (09XK)
   and `lemma-characterize-henselian-pair` (09XI), including the (3) implies (1) argument,
   in the locally available Stacks source. Integrality of `AdjoinRoot f` uses monicity,
   finite-implies-integral and transitivity; `Ideal.map_map` supplies the correct extended
   ideal. All three proof imports are used directly. Every old proof dependency remains used,
   so `No longer needed` has no missing node or module. Read `dag/units/sk-thm-p1.json`:
   this supporting algebra lemma is below its realized steps, and the curve/strictly
   henselian comparison route is preserved. Edge cases introduce no extra hypotheses:
   zero rings are allowed, `I = 0` works, and degree-zero monic polynomials or a factor
   equal to `1` are covered by the quotient and factorization statements.
5. **DAG agrees — repaired.** The four recorded proof steps now match the Lean proof:
   Jacobson containment; integral idempotent lifting in `AdjoinRoot f`; the inlined Bezout
   reduction and monic-factorization theorem; the reverse factorization criterion.
   Added the already existing Mathlib-leaf node
   `lem-weil-pbc-integral-maximal-contracts-maximal` to step 1 and `proof_deps`:
   its algebra form is precisely the theorem called at Mathlib `Ideal/GoingUp.lean:204`.
   The dependency list is the union of the steps' `uses`, and `proof_origin` names 09XK
   and the 09XI conversion. There are no new nodes requiring additional fields.

Changes in this reading: corrected the stale DAG reference to the removed private helper,
recorded the missing maximal-contraction dependency, expanded the theorem's proof docstring
to describe its actual simple-root conversion, and clarified the added plain imports in this
report. The verified Lean proof itself was retained.
