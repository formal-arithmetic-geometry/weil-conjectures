## What changed

Proved `MvPolynomial.ideal_coefficients_monomial_membership` in the item's module.
The proof uses finite span-range expansion, MvPolynomial coefficient formulas, span induction
for coefficient ideals, and the finite monomial decomposition `p.as_sum`. Removed the two unused quotient imports. No new imports or
declarations were added. The node proof was updated to record the two proof steps.

## Proved and sorry left

Closed the sole sorry, `MvPolynomial.ideal_coefficients_monomial_membership`.
No sorry remains and no new sorry was added.

## No longer needed

Removed unused imports `Mathlib.Algebra.Quotient` and
`Mathlib.RingTheory.Ideal.Quotient.Operations`. No DAG proof nodes or Sheaf modules
were dependencies of the original node, so none of those can be pruned here.

## Where the brief, the DAG or earlier work was wrong

The DAG proof was only a high-level split; the concrete span-range and monomial-support
steps are supplied directly in the Lean proof. The statement and hypotheses are unchanged.

The public import pruning is recorded in
`coord/changes/polynomial-ideal-membership-imports.md`. Both direct importers already
import both quotient modules explicitly, so no forced adaptation is needed.

## Second reading by M4

1. PASS: compared the delivered module with the repository and checked the entire
   declaration header byte for byte. The signature, hypotheses, conclusion, docstring,
   visibility, and definitions are unchanged. The public import removals have the
   supplied change record. Both direct importers independently import both removed
   quotient modules and compile unchanged against the delivered module.
2. PASS: local compilation succeeds without errors or warnings. A scratch copy with
   `#print axioms MvPolynomial.ideal_coefficients_monomial_membership` reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`. The delivered module has no `sorry`,
   forbidden declaration, hollow definition, or data selected from an unproved theorem.
3. PASS: no statements or nodes were split off. Read both directions: the forward
   coefficient formula vanishes at exponent zero; the reverse induction factors a
   generator monomial using the positive exponent. Edge cases `i = 0`, `E = 0`,
   zero generators, and the zero ring all obey this argument without extra assumptions.
4. PASS: searched Mathlib and both library roots with coefficient/ideal/monomial
   variants and ran LeanFinder with a divisibility-based query. The closest results
   concern unit-coefficient monomial generators or constant coefficient ideals;
   neither replaces this criterion with arbitrary `g j` and exponent-dependent ideals.
   The existing direct proof is appropriate and both retained imports serve the
   statement. The old `proof_deps` is empty, so no DAG dependency is missing from
   `## No longer needed`. The node is below the unit level and is absent from the
   `sk-thm-p1` unit's `realized` statement and steps; no unit route is bypassed.
5. PASS: parsed both node JSON files: only `proof` differs substantively. Its two
   elementary steps describe the actual coefficient expansion and span induction;
   empty `proof_deps` and the unchanged source-based `proof_origin` are accurate.

Second reading changed only JSON serialization back to literal Unicode to keep the
node diff focused, corrected the importer inventory after the dry run refreshed
the repository (the map module now also imports this criterion), and appended this
review. No proof repair was necessary.
