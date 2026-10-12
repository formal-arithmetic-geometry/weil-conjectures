## What changed

Proved `MvPolynomial.polynomial_origin_regularLocal`, preserving its complete public
signature and visibility byte for byte. Two proved private helpers, `origin_ker` and
`origin_maximal`, identify the variable ideal with the kernel of evaluation at zero and
establish maximality. The quotient isomorphism is constructed by the first isomorphism
theorem; no data is chosen from an unproved existence theorem.

Replaced the proof-only import `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso` with
proof-only imports `Mathlib.RingTheory.RegularLocalRing.Polynomial` and
`WeilConjectures.Mathlib.RingTheory.KrullDimension.Polynomial`. All four public imports
remain unchanged and supply the notions in the statement. The proved upstream theorem
`MvPolynomial.height_eq_of_isMaximal` gives height d; Mathlib supplies localization
dimension, regularity, and the maximal ideal. Mapping the span gives its generators.
The DAG proof and proof dependencies describe this route.

## Proved and sorry left

Closed the one existing hole: `MvPolynomial.polynomial_origin_regularLocal`
(node `lem-weil-pbc-polynomial-ring-origin-regular-local`). No holes remain in the item;
none were added or split off. `origin_ker` and `origin_maximal` are proved helpers.
This is a proof, not a decomposition. The new node only records an already proved
upstream declaration. The zero-variable case has the zero ideal in a field, quotient k,
and a dimension-zero field localization; d=1 gives the usual origin of the affine line.
The proof works over fields of every characteristic.

Local compilation through lcompile.py passes without errors or warnings. Explicit
scratch #print axioms checks cover the public theorem and both private helpers;
the delivery tool also probes every declaration.

## No longer needed

Removed import/module `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso` and its node
`lem-weil-pbc-localization-prime-residue-field-iso`: direct height/dimension equality
replaces transporting prime chains. Also removed every other old proof dependency
absent from the new proof: `def-weil-pbc-noetherian-ring`,
`lem-weil-pbc-finite-type-algebra-noetherian`, `lem-weil-pbc-localization-noetherian`,
`lem-weil-pbc-noetherian-local-dimension-le-generators`, and
`lem-weil-pbc-polynomial-ring-domain`. These are pruned from this caller only; this
report does not assert that other target branches stop using them.

The second reading additionally removed the proposed private `origin_height` induction
and the undelivered node `lem-weil-pbc-polynomial-maximal-height-successor`; the upstream
maximal-height theorem supplies their entire use.

## Where the brief, the DAG or earlier work was wrong

The statement is correct. The DAG's six-step chain argument can be shortened using
proved height and regularity theorems. The first worker correctly found a Mathlib height
successor theorem but missed the upstream `MvPolynomial.height_eq_of_isMaximal`.
No definition, public interface, target statement, or other held module changed.

The first worker consulted Stacks Tag 00OP online because the local literature checkout
lacks algebra.tex. The second reading inspected the pinned upstream and Mathlib proofs.
Semantic search and Loogle do not index the upstream maximal-height result; local
source search finds it. No new unproved statement is required.

## New nodes

`lem-weil-pbc-mv-polynomial-maximal-height` records the proved upstream declaration
`MvPolynomial.height_eq_of_isMaximal`, with its field, variable-count, and maximality
hypotheses. Its source proof inducts on the variable count using Jacobson contraction
and Mathlib's height successor theorem. LeanSearch (unavailable), Lean Finder, Loogle, and local grep searches
are recorded; no previous DAG node carries this declaration. There is no new Lean
module, proof obligation, or change record.

## Second reading by J3

1. Compared the entire delivered module with the repository version. The existing
   public theorem signature is byte-for-byte identical, including its existential
   maximality proof and all five conclusions. Public imports and visibility are
   unchanged; no definitions or existing statements changed. Verdict: pass.
2. Compiled the original worker proof and the simplified proof through lcompile.py.
   Both pass without errors or warnings. Scanned for sorry, axiom, unsafe, opaque,
   implemented_by, and extern: none occur. Explicit #print axioms probes show only
   propext, Classical.choice, and Quot.sound for the target and private helpers.
   The quotient equivalence is a real construction. Verdict: pass.
3. No statements are split off with sorry. Checked the new node against the existing
   upstream theorem and its proof, searched for an existing node and a shorter result,
   and checked n=0 and n=1 and arbitrary field characteristic. Verdict: pass.
4. Read from the target downward. Found the shorter upstream maximal-height theorem,
   replaced the induction with its application, and kept only the two evaluation
   helpers. The direct zero-evaluation induction avoids an additional upstream import
   solely to reuse the more general ker_eval theorem. Both new imports are proof-only.
   Checked the old proof_deps against No longer needed: all six removed nodes are
   listed. The item is absent from sk-thm-p1's binding realized entries, and no unit
   statement, step, realization, or chapter route changes. Verdict: pass.
5. Checked the existing node diff: only proof, proof_deps, and proof_origin change.
   Proof dependencies equal the union of the steps' uses and match the Lean route.
   The new node records an existing proved declaration, source, proof, three searches,
   creation provenance, blueprint ancestry, chapter, unit, and Lean metadata.
   The dry run identified two metadata faults, repaired before delivery: recorded the
   attempted LeanSearch query (service unavailable), and removed lean.file because
   this node registers an existing declaration rather than delivering a new module.
   Verdict: pass.

Second-reading changes: removed origin_height and the proposed successor-height node;
added the proof-only upstream import, applied height_eq_of_isMaximal directly, recorded
its existing-declaration node, and updated the proof docstring, DAG, and this report.
