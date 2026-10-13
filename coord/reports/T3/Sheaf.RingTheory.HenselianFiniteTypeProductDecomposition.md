## What changed

Filled `HenselianLocalRing.finiteType_exists_algEquiv_pi_prod` in
`Sheaf.RingTheory.HenselianFiniteTypeProductDecomposition` without changing its signature,
visibility, imports, or docstring. A proved private helper `HenselianLocalRing.etale_retraction`
lifts the base ring to `ULift.{v} R`, transfers henselianity by a ring equivalence, applies
`existsUnique_algHom_of_henselianLocalRing_etale`, and maps the retraction back to R.
Surjectivity of the residue map proves the lifted residue-field bijectivity; contraction
of the maximal ideal is preserved by the ring equivalence.

The main proof applies `Algebra.etale_retraction_finite_type_splitting`, then
`finite_algebra_is_product_local_rings` to its finite factor. `Module.Finite.equiv` and
`Module.Finite.of_pi` prove finiteness of each local factor, and `AlgEquiv.prodCongr`
composes the decompositions. The bad factor and its finite-type instance are retained
verbatim from the splitting theorem. This also handles the empty product and zero bad
factor without adding nontriviality hypotheses.

Validation: the module compiles cleanly through lcompile.py with no warnings.
The proof follows the existing four-step DAG plan; no route or dependency changes.

## Proved and sorry left

Closed the sole original hole:
`HenselianLocalRing.finiteType_exists_algEquiv_pi_prod`
(node `lem-weil-pbc-henselian-finite-type-product-decomposition`).
One of one original sorries closed; zero new holes, zero split-off statements.
No sorry remains in the delivered module. The private helper is fully proved.
The proof still uses the existing named dependency
`Algebra.etale_retraction_finite_type_splitting`, whose sorry remains in its own,
undelivered module; this delivery does not claim to close that lower dependency.

## No longer needed

None. All three existing proof-dependency imports remain necessary:
`Sheaf.RingTheory.HenselianEtaleRetraction`,
`Sheaf.RingTheory.EtaleRetractionFiniteTypeSplitting`, and
`Sheaf.RingTheory.EtaleRetractionFiniteProductLocal`.
No nodes or modules of the recorded plan are pruned, and no imports are added.
The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface correction. The same-universe henselian retraction statement
needs a proved universe bridge before it can supply the test hypothesis ranging over
`Type (max u v)`; the private ULift helper supplies that glue without altering any statement.
Searches through leanfinder, loogle, msearch grep, and the source library found no shorter
finite-type product decomposition. Mathlib supplies the elementary finiteness transport
and product-isomorphism assembly used in the proof.

## Second reading by T3

1. **Diff and interfaces.** Compared the delivered module with the repository version. The theorem signature, visibility, docstring, imports, and public declarations are unchanged; only the proof and a private helper were added. Verdict: pass.
2. **Compilation and proof integrity.** Compiled the module with `lcompile.py`; it succeeds with no warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations, and no hollow definitions. Verdict: pass.
3. **Statements and dependencies.** The existing target statement is unchanged and no statements were split off. The helper is private and fully proved. The proof uses the recorded retraction, finite-type splitting, and finite-product-local dependencies; no shorter library result was found. Verdict: pass.
4. **Pruning and route.** All imports remain necessary for the proof or public statement. The four-step DAG route is preserved: henselian retraction, finite-type splitting, finite local product, and assembly. No nodes or modules can be pruned. Verdict: pass.
5. **DAG/report consistency.** The existing node's proof plan and dependency list agree with the implementation; no new node or change record is needed. The report accurately records one hole closed and none added. Verdict: pass.

Changed only the proof of `HenselianLocalRing.finiteType_exists_algEquiv_pi_prod` and added the private universe-bridging helper `etale_retraction`; appended this second-reading record. No interface or dependency changes were required.
