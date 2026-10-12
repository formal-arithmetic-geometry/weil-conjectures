## What changed

Proved `CategoryTheory.BigradedExactCouple.halfPlaneGradedCanonical` in
`Sheaf.CategoryTheory.HalfPlaneGradedCanonical` without changing its signature.
Extract the half-plane convergence witnesses and weak convergence, then combine
`g_factors_limitCycles`, the two epimorphism properties, the kernel equality,
and `weakConvergence_comparison`. Updated the existing node's proof route.
The theorem-scoped unused-variable linter option preserves the original named
existential proof binders `hA` and `hConv`, which are unused in the statement.

## Proved and sorry left

Closed: `CategoryTheory.BigradedExactCouple.halfPlaneGradedCanonical`
(node `lem-sp-half-plane-graded-canonical`), the module's only hole.
No holes remain in the item; no holes or new declarations were added elsewhere.
The proof uses existing holed declarations `halfPlaneConvergence`,
`g_factors_limitCycles`, and `weakConvergence_comparison`; those remain the
existing downstream work (nodes `thm-sp-half-plane-convergence` and
`def-sp-convergence`). This delivery does not claim their proofs are complete.

## No longer needed

Removed direct imports:
- `Sheaf.CategoryTheory.DerivedCoupleExact`
- `Sheaf.CategoryTheory.ExactCouple`
- `Sheaf.CategoryTheory.ExactCoupleConvergence`

The direct proof dependency `lem-sp-derived-couple-exact` is unnecessary here:
its stabilized-page calculation is already encapsulated by half-plane convergence.
The direct proof dependency `def-sp-exact-couple` is unnecessary for the proof;
its definitions remain accessible through the unchanged public import.
`def-sp-convergence` remains a proof dependency; its module is publicly reexported
by `Sheaf.CategoryTheory.HalfPlaneConvergence`, so its separate import is redundant.
None of these modules is claimed to leave the entire target import closure:
HalfPlaneConvergence still imports DerivedCoupleExact and ExactCouple, and publicly
imports ExactCoupleConvergence. No unit statement or step is bypassed; the unit
record `sk-prop-av-pqf-finite` has no realized nodes.

## Where the brief, the DAG or earlier work was wrong

The DAG's repeated stabilized-page argument is unnecessary for the current Lean
statement: `halfPlaneConvergence` supplies `ConvergesTo`, whose definition already
includes the required epimorphisms and equal kernels through weak convergence.
The existing comparison theorem supplies uniqueness. No mathematical dispute or
statement correction is needed. The referenced unit source file is absent in this
clone; the unit JSON was read and has empty realized statements and steps.

## Second reading by J1

1. PASS: Compared the only delivered module with the repository using `diff` and
   checked the existing theorem signature byte for byte with a script. No signature,
   definition, public import or target statement changed; no change record is needed.
2. PASS: Compiled the module locally through `lcompile.py`, without errors or warnings.
   A scratch copy with `#print axioms` reports exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The latter comes from existing open dependencies;
   the delivered module has no `sorry` and no forbidden declaration or implementation
   escape. It constructs no new data from an unproved existence theorem.
3. PASS: No statements were split off, and no new declarations or nodes were added.
   Checked the conjunction projections against `ConvergesTo`, `AbutsTo` and
   `WeaklyConvergesTo`; all conclusions are supplied at every bidegree. Zero objects
   and boundary indices p = 0, q = a require no extra inference or exception.
4. PASS: The reduction uses the existing half-plane convergence and canonical
   comparison declarations directly. Searched the library by declaration and concept,
   and Mathlib with the independent query `epi.*kernel|kernel.*epi|iso.*kernel`;
   no shorter exact-couple-specific route was found. The sole public import provides
   the statement's types; no proof-only import is public. All unused old proof
   dependencies are listed above, including both pruned nodes. The unit JSON has
   empty realized statements and steps, so no realized unit route is bypassed.
5. PASS: Compared the node with the repository; only `proof`, `proof_deps` and
   `proof_origin` change. The two proof steps match the Lean code and their union
   of dependencies is exactly `thm-sp-half-plane-convergence`, `def-sp-convergence`.

Second-reader repair: updated the theorem's proof docstring to describe the actual
reduction through convergence, rather than the unused stabilized-page calculation.
The proof, signature, node and imports needed no further repair. Closed one existing
hole and added zero; the declaration remains conditional on the existing open
convergence results, as recorded above.
