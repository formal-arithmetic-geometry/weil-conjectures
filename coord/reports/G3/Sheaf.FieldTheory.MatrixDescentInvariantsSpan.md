## What changed

Proved `Field.matrixDescentInvariants_span` with its statement and visibility unchanged in
`Sheaf.FieldTheory.MatrixDescentInvariantsSpan`. Added a proved private helper,
`Field.finite_factorization`, and proof-only imports of
`Sheaf.Topology.ContinuousOpenNormalStabilizer`,
`Mathlib.FieldTheory.Galois.Profinite`, and
`Mathlib.LinearAlgebra.Basis.VectorSpace`.

The helper factors b through restriction to a finite Galois subfield. The proof explicitly
constructs weighted sums of twisted matrix units, proves their invariance by reindexing,
and uses Mathlib independence of characters and a separating linear functional to show
each matrix unit lies in the invariant span. The matrix-unit expansion proves the result
for every n, including n=0, and every characteristic. No division by a group order occurs;
no assumption b(1)=1 is added. The finite field is obtained inside a proposition proof,
and the averages are explicit finite sums; no definition chooses arbitrary data from an
unproved existence theorem.

Updated the existing node `lem-sc-matrix-descent-invariants-span` only in `proof`,
`proof_deps`, and `proof_origin` to describe the implemented route. No interface change,
forced adaptation, new module, or new node is needed.

The tool node `lem-exc-coinduced-functions-open-stabilizer`, in unit `sk-prop-h2`, supplies
only the general profinite right-stabilizer lemma. It is used as a tool, not as a replacement
of the route of unit `sk-thm-br`; that unit's realized statement/step lists are empty, and
its Brauer-injectivity/Tsen route is untouched. The original invariant-algebra definition
node remains used. Searches through leanfinder, loogle, launcher grep, and local rg found
no existing full descent theorem; the key shorter-route results are Mathlib's
`linearIndependent_monoidHom` and `Submodule.exists_le_ker_of_notMem`.

## Proved and sorry left

Closed the single hole `Field.matrixDescentInvariants_span`
(node `lem-sc-matrix-descent-invariants-span`): 1 of 1 original holes closed.
The private helper `Field.finite_factorization` is proved as well.
No sorry remains in the delivered module. No holes were added or split off.

This is a proof from an existing stated dependency, not a decomposition introducing new
holes. It still rests on the pre-existing sorry in
`ProfiniteGrp.exists_openNormalSubgroup_right_invariant`
(node `lem-exc-coinduced-functions-open-stabilizer`, module
`Sheaf.Topology.ContinuousOpenNormalStabilizer`). That declaration is not changed here.
All linear algebra, lifting, Krull topology, and finite-group reindexing steps after the
stabilizer application are proved using Mathlib and explicit Lean calculations.

Validation: the module compiles locally without errors or warnings (about 10 seconds).
`deliver3.py G3 Sheaf.FieldTheory.MatrixDescentInvariantsSpan --no-push` printed
`OK (dry run)`: compilation and preflight passed except for the second reading, which
the independent second reader supplies. Nothing was pushed.

## Second reading by G3

1. **Visibility and statements.** Compared the delivered module with the repository
   version line by line. The public imports needed by the statement and all existing
   declaration signatures are unchanged; only proof-only imports, the private helper,
   and proof bodies differ. Verdict: passes.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it has no errors,
   warnings, `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`.
   A scratch `#print axioms Field.matrixDescentInvariants_span` reports only the
   permitted axioms plus the pre-existing `sorryAx` from
   `ProfiniteGrp.exists_openNormalSubgroup_right_invariant`. The delivered theorem
   itself introduces no new hole. Verdict: passes.
3. **Statements and split-offs.** No statement was split off and no new node was
   added. The private finite-factorization helper is a proved construction from the
   existing open-stabilizer theorem, with no arbitrary witness hidden in a definition.
   The matrix-unit and weighted-sum argument proves the original conclusion for all
   `n`, including `n = 0`, without adding hypotheses or weakening the result. Verdict:
   passes.
4. **Route and pruning.** The proof uses the existing invariant-algebra definition
   and the stated open-stabilizer dependency, then follows the finite quotient,
   weighted orbit sums, character independence, and matrix-unit expansion recorded in
   the node. No old proof dependency is unused; only trial imports that were redundant
   with retained imports were removed. Verdict: passes.
5. **DAG agreement.** The node's `proof`, `proof_deps`, and `proof_origin` match the
   implemented route, while its statement and unit are unchanged. The unit's route is
   preserved, and no target or dependent interface is altered. Verdict: passes.

The second reading changed only this report section; no Lean or DAG repair was needed.

## No longer needed

No original import, named dependency node, or module was pruned: the original imports
are needed by the public statement/definitions. Removed trial proof imports
`Mathlib.LinearAlgebra.LinearIndependent.Lemmas`,
`Mathlib.LinearAlgebra.LinearIndependent.Basic`, and `Mathlib.Data.Matrix.Basis`:
the retained imports already expose their required declarations. These are trial-import
cleanup, not newly pruned modules from the original target closure.

The old plan's coefficient-field shrink, descent of the whole space Mat_n(L), identification
of its full invariant subalgebra, and separate proof that Mat_n(L) spans Mat_n(S) are
unnecessary. Factoring b is enough on matrix units, and an S-linear separating functional
allows the independence argument directly over S. None of those omitted constructions
was a separate named proof dependency of this node.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The original plan asked for more
finite-field descent infrastructure than the spanning conclusion needs. Its steps 1--3
had no stated nontrivial dependencies beyond the invariant-algebra definition; the
implemented proof supplies their algebraic content and uses the existing profinite
stabilizer tool for the topological input.

The repository's downloaded literature directories are absent on this machine, so the
source context was read at https://stacks.math.columbia.edu/tag/03R6 and
https://stacks.math.columbia.edu/tag/04JP. Tag 03R6 is a sketch of the classification of
central simple algebras by PGL cohomology; it does not spell out this weighted-sum proof.
The existing node already identifies the finite descent expansion as agent-written.
The updated proof_origin retains that distinction. The original declaration docstring
is retained as the earlier, valid proof plan; the node now records the implemented
shorter argument.
