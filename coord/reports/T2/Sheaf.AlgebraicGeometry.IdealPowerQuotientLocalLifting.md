## What changed

The existing theorem `AlgebraicGeometry.Scheme.ideal_power_quotient_local_lifting`
keeps its signature byte for byte. Its first conjunct now follows directly from
`ideal_power_evaluation_eventually_zero` applied to `cokernel (a n)`, after installing
`hqc n` and `Modules.isQuasicoherent_cokernel (a n)`. Associativity and `zero_comp`
then supply the required quotient transition. Its second conjunct uses the one
new split theorem `ideal_power_quotient_local_lifting_section`, in the separate module
`Sheaf.AlgebraicGeometry.IdealPowerQuotientLiftingSection`.

The target adds only plain proof imports for these two modules and the upstream
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`. Its original
public imports stay because they supply the signature's quasi-coherence/finite-type,
ideal-power, and quasi-separatedness notions. The new module has only those signature
imports. No existing statement, definition, or public import was changed.

## Proved and sorry left

Closed existing hole: `AlgebraicGeometry.Scheme.ideal_power_quotient_local_lifting`
(node `lem-weil-pbc-ideal-power-quotient-local-lifting`).
Added hole: `AlgebraicGeometry.Scheme.ideal_power_quotient_local_lifting_section`
(node `lem-weil-pbc-ideal-power-quotient-local-lifting-section`). It is exactly the
lifting conjunct, not a restatement of the conjunction.

This is a decomposition: one existing hole closed and one new hole added, net zero
within these delivered files. The first conjunct uses the already-open upstream
`ideal_power_evaluation_eventually_zero`; it is not independently axiom-free.
`#print axioms` for both delivered theorems lists only `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx`. The cokernel-closure theorem itself has only the three
standard axioms. No other sorry, new definition, or chosen data is introduced.

Compared with the first worker's sandbox, the extra sorry
`ideal_power_quotient_local_vanishing` and its new node are removed entirely.

## No longer needed

No import was removed and no module is claimed as globally pruned.
All six old direct proof dependencies of the target were inspected:
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-spec-module-tilde-sections`,
`lem-weil-pbc-quasi-coherent-module-cokernel-image`,
`lem-weil-pbc-glue-sheaves-of-modules`,
`def-weil-pbc-module-localization-away`, and
`lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings`.
They are no longer direct dependencies of the target's written proof; they remain
in the lifting split's sourced proof plan, so they are not globally unnecessary.
The target's new direct dependencies are cokernel closure, eventual zero, and the
lifting split. The first worker's new vanishing node is not delivered.

## Where the brief, the DAG or earlier work was wrong

The first worker missed the existing eventual-zero theorem, duplicated both conjuncts
as new sorries, left their proof dependencies pointing back to the original theorem,
and did not update the original node. Those back edges would form a circular proof
plan once the original node recorded its actual use of the conjuncts. The split nodes'
statements were not self-contained, their comments were not full docstring proofs,
and the original theorem's docstring was attached to the newly inserted vanishing
lemma. The initial report described a proof where only a decomposition had occurred.
These issues are repaired below. No mathematical error in the original theorem or
source was found.

## New nodes

`lem-weil-pbc-ideal-power-quotient-local-lifting-section` is the sole new node. It states
only section lifting, in its own Lean module, with the original hypotheses and full
self-contained statement. Its proof plan spells out the affine monomial construction,
annihilator quotient identification, finite overlap comparison using eventual zero,
and gluing. There is no dependency on the original conjunction. No change record is
needed because no existing signature, definition, or public import changes.

## Second reading by T2

1. Compared the two delivered modules with the repository. The new module is absent
   there; the original theorem's signature was compared programmatically and is
   byte-for-byte identical. The original docstring remains attached to the original
   declaration. All changes to the original module are proof text and plain imports.
   Verdict: no accidental interface or target change.
2. Compiled both files in import order through `lcompile.py --all`, with no errors or
   warnings after replacing unnecessary `letI` with `let`. A scratch copy appended
   `#print axioms` for both delivered theorems, eventual zero, and cokernel closure.
   Results are recorded above; no forbidden axiom or declaration form occurs, and
   there is exactly one delivered sorry, the named lifting theorem. No definition
   is added and no arbitrary data is chosen from an unproved existence theorem.
   Verdict: valid reduction with explicitly open dependencies.
3. Read Stacks tags 01PM and 01PQ, the existing eventual-zero declaration, the
   quasi-coherent cokernel/image theorem, and the finite-cover and gluing statements.
   The retained split is the strict second conjunct of 01PQ. Its finite-type ideal
   hypothesis supplies finitely many generators and localization of annihilators;
   quasi-coherence supplies tilde models and cokernel closure; compactness supplies
   the finite main cover; quasi-separatedness supplies finite affine overlap covers.
   The equations for r and q, plus cancellation, preserve evaluation and comparisons.
   Checked empty X, zero ideal (positive power, empty complement), unit ideal
   (degree-zero section map), zero section, and the positive exponent k needed for
   the monomial bound. On a principal affine complement the fraction formula reduces
   to multiplying by a sufficiently high power of its generator. No extra finiteness
   assumption on F is used. The docstring now gives the complete construction.
   Searched Lean/Sheaf and the upstream algebraic-geometry library using quotient,
   annihilator, and power terminology; found the usable eventual-zero and upstream
   cokernel-closure lemmas but no duplicate of the remaining lifting assertion.
   Real `msearch.py` LeanFinder and Loogle searches returned related localization or
   adic-quotient statements, grep returned no match in Mathlib's modules folder;
   LeanSearch returned Internal Server Error, recorded as unavailable. Verdict: true,
   sourced, strictly smaller split, with no known existing replacement.
4. Used the shorter upstream cokernel-closure declaration rather than importing the
   larger conjunction of affine cokernel/image facts into the target. The written
   first-conjunct proof simply installs the quasi-coherent instance, applies eventual
   zero, and composes with q. Proof imports are plain, and remaining public imports
   provide signature notions. Inspected `dag/units/sk-thm-p1.json`: this item is not
   any of its realized statement/step nodes; all its curve-calculation, strict-henselian,
   and exchange nodes stay unchanged. The affine lifting/overlap/gluing source route
   is retained below that unit. Every former direct dependency is accounted for in
   No longer needed. Verdict: shortest available reduction, no unit bypass or pruning
   overclaim.
5. Updated the original node's proof, proof_deps and proof_origin to match the actual
   two-branch proof. Rewrote the sole new node's self-contained statement, verbatim
   Lean signature, module/file record, sourced steps, dependency union, blueprint
   ancestry, and real search records. Its dependencies are lower ingredients, never
   the original conjunction. The removed vanishing node is absent. Verdict: DAG and
   Lean agree and contain no new circular proof plan.

Second reading changed: removed the vanishing split and proved that branch from
existing declarations; moved the remaining split into its own module; repaired its
source proof docstring, both DAG records, search evidence, original docstring placement,
and progress/pruning accounting. No existing signature changed.
