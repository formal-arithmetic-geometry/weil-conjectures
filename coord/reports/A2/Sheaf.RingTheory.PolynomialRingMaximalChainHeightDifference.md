## What changed

Proved `MvPolynomial.maximalChain_height_difference` in
`Sheaf.RingTheory.PolynomialRingMaximalChainHeightDifference`, with its signature and
visibility unchanged. The proof follows Stacks 00OR: bound heights using a containing
maximal ideal and the existing maximal-localization dimension theorem, choose a longest
prefix, concatenate with the supplied saturated chain, transfer to the localization at
its last prime, and apply the existing Cohen–Macaulay maximal-chain theorem.

Four proved private helpers supply the glue: `regular_depth` extracts dimension-many
maximal-ideal generators and uses their regularity to bound depth;
`saturated_of_full_height` obtains minimality and saturation from Mathlib's height/index
formula; `smash_saturated` checks the concatenation; `saturated_isMaxChain` proves
maximality by the least index above any proposed additional element. No arbitrary data
is defined from an unproved existence theorem. The witnesses used locally come from
proved Mathlib existence statements.

Added the proof-only import `Mathlib.RingTheory.RegularLocalRing.Polynomial` for regularity
of polynomial rings and their prime localizations. Removed the redundant direct import
`Sheaf.RingTheory.Depth`; its definitions remain available through the retained
`Sheaf.RingTheory.MaximalChainLengthOfDepth` import. Updated the item's DAG proof and
proof dependencies to describe the actual chain argument. No public import, statement,
definition, target, or other module was changed. The unit `sk-thm-p1` and its realized steps
are untouched.

Local single-file compilation succeeds without warnings. The argument covers zero
variables, height zero, equal endpoints, and length-zero chains: no positivity hypothesis
is introduced in the main theorem; the least-index argument handles index zero separately.

## Proved and sorry left

Closed the one original hole:
`MvPolynomial.maximalChain_height_difference`
(node `lem-weil-pbc-polynomial-ring-maximal-chain-height-difference`).

Added zero holes. No `sorry` remains in the delivered module, including its private helpers.
The proof uses the existing declaration
`IsLocalRing.maximal_chain_length_eq_of_depth`
(node `lem-weil-pbc-cm-local-maximal-chain-length`), which is still `sorry` in the library.
Thus this delivery removes the upper hole relative to the project's existing lower
statements; it does not claim that all its transitive dependencies are already proved.

## No longer needed

Removed the redundant proof import `Sheaf.RingTheory.Depth`. The module itself stays
needed transitively, and `def-weil-pbc-depth` remains a proof dependency.

Pruned the proof dependency `lem-weil-pbc-polynomial-ring-domain`: the longest prefix has
a minimal head directly by height zero, so the proof does not need to identify it with
`(0)` using the domain property. Its Mathlib module
`Mathlib.Algebra.MvPolynomial.Basic` is still a public statement import and is not pruned.
No further modules or nodes are made unnecessary by this delivery.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The original six-step docstring gives
the source plan; the implemented step 4 uses the more general order-theoretic minimal-head
argument rather than its explicit domain argument. The DAG now records this refinement.
The depth argument also records its existing regular-system-of-parameters definition node
explicitly. All proof-dependency modules used are available in the compiled library.

## Second reading by A2

1. **No accidental interface changes.** Compared the delivered module with the repository version. The
   public theorem signature and visibility are byte-for-byte unchanged; only proof imports, private
   helpers, and the proof body changed. The DAG edits only record the actual proof route and removed
   dependency.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it compiles without errors or
   warnings. No `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` occurs in the
   delivered module. The target's only `sorryAx` comes from the already-open imported theorem
   `IsLocalRing.maximal_chain_length_eq_of_depth`; the new proof introduces no hole.

3. **Statements and edge cases.** The target statement is unchanged and the private helper claims
   are direct order-theoretic facts used by the proof. The finite-set generator construction is
   genuine, with no data selected from an undetermined existence proof. The argument handles
   `n = 0`, height zero, equal endpoints, and length-zero chains without added positivity assumptions.

4. **Shortest route and pruning.** Checked the existing proof dependencies and Mathlib search record.
   The proof uses the stated regular-local and localization route, while replacing the unnecessary
   domain-prefix identification with `Ideal.exists_ltSeries_length_eq_height` and removing the
   redundant public proof import `Sheaf.RingTheory.Depth`. The removed polynomial-domain node is
   absent from `proof_deps`; the unit `sk-thm-p1` and its realized route remain intact.

5. **DAG agreement.** The node's proof steps, proof dependencies, and proof origin match the Lean
   proof, including the finite-generator depth argument, the saturated-prefix construction, and the
   localization order-isomorphism/maximal-chain argument. No new split-off statement or node was
   added.

**Changes made during second reading:** added this review record only; no Lean proof or statement
changes were necessary.
