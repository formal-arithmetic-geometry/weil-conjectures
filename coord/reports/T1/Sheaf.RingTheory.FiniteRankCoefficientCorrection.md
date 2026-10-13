## What changed

Replaced the sole `sorry` in `Sheaf.RingTheory.FiniteRankCoefficientCorrection` with a
complete Lean proof, preserving its signature and visibility. Added the proof-only import
`Sheaf.RingTheory.FiniteRankDefectDerivation` and updated the item's node to match the proof.

The proof constructs the discrepancy additive map and verifies its ideal membership and
Leibniz identity. After obtaining a finite-error derivation, it constructs the actual ring
endomorphism `beta(x) = x + D(r(x))`. Multiplicativity follows from `(ker r)I = 0`.
Composing beta with the original section gives the corrected section. The universal
property of subring closure transports every coefficient expression at once: beta fixes
all elements of t and sends each original coefficient section value to its corrected value.
The final span membership is then an additive identity.

The differential-basis argument of original steps 1--3 is isolated in the new generic
module `Sheaf.RingTheory.FiniteRankDefectDerivation`. Its statement takes an arbitrary
ideal-valued derivation, with no local-ring condition, finite ideal generators, coefficient
subfield, psi, or ring-closure hypothesis. It produces an additive derivation and finite
error family, without asserting a section or coefficient-closure conclusion. The current
module proves those missing parts and constructs the input discrepancy; this is a strict
reduction of the original argument.

Both modules compile cleanly through lcompile.py. No definitions or existing signatures
changed. No forced adaptations are needed. The new theorem has its full natural-language
proof and source in its docstring and a matching new DAG node.

## Proved and sorry left

Closed: `Algebra.exists_finite_rank_coefficient_correction`
(node `lem-weil-pbc-finite-rank-coefficient-correction`), the original module's one hole.
There are no `sorry`s left in the item's module.

Added: `Algebra.exists_finite_rank_defect_derivation`
(node `lem-weil-pbc-finite-rank-defect-derivation`), in its own new module.
Its proof is exactly `:= by sorry`.

This delivery is a decomposition: one upper hole closed and one strictly smaller hole
added, hence net zero holes closed. The original result still depends on sorryAx through
this single named intermediate theorem. No claim of an axiom-free completed result is made.

## No longer needed

The full node `lem-weil-pbc-jacobi-zariski-homology-sequence` and module
`Sheaf.RingTheory.JacobiZariskiHomologySequence` are unnecessary for this argument.
Its left-end exactness, presentation comparison, coefficient formula, Tor criterion, and
base-changed kernel isomorphism are not used. The new differential lemma's plan uses only
`lem-weil-pbc-jacobi-zariski-middle-exactness`, an existing Mathlib leaf, specifically
`Algebra.H1Cotangent.exact_δ_mapBaseChange`. The new module imports
`Mathlib.RingTheory.Kaehler.JacobiZariski` as a proof-only import.

`def-weil-pbc-kahler-differentials` moves from the item's direct proof dependencies into
the new lemma's proof dependencies; its notion and universal property remain needed.
No original imports were removed: all three public imports support the unchanged signature.
A trial proof-only import of `Mathlib.Tactic.Ring` was removed after clean recompilation
without it. No other proof-only import remains unused.

This describes pruning of this argument, not global unreachability: other items may still
need the full homology-sequence module or its dependencies. The unit's statement and all
its realized proof steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original node's reference to the full Jacobi--Zariski homology sequence is unnecessarily
large. Its middle exactness clause is already in Mathlib, with an existing leaf node, and
suffices for the finite-support argument. The source proof and statement are mathematically
consistent; no statement correction is proposed.

Original step 4 can be implemented by the explicit global ring endomorphism beta, avoiding
any choice of a polynomial expression and any expression-independence argument. This keeps
the same mathematical route: add the residue derivation to the section, fix the maximal-ideal
generators, and reevaluate coefficients.

The local source file `literature/stacks-project/smoothing.tex` is absent on this machine.
I read the source at https://stacks.math.columbia.edu/tag/07FG, especially the paragraphs
choosing theta, the differential basis, J0, and D. Searches via msearch.py used LeanFinder,
Loogle, grep, and LeanSearch. LeanFinder returned characteristic-zero differential-field
extensions and cotangent maps; grep found no finite-error extension theorem. Loogle's
query did not recognize H1Cotangent. LeanSearch returned Internal Server Error and is
recorded as unavailable. Local DAG, Sheaf, and WeilConjectures searches found the existing
middle-exactness leaf, but no generic finite-rank derivation theorem. A whole-blueprint
search for derivation returned six unrelated nodes.

## New nodes

`lem-weil-pbc-finite-rank-defect-derivation`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-rank-defect-derivation.json`, states
precisely the differential argument remaining from original steps 1--3. Its field extension,
residue action, ideal annihilation, derivation identities, finite first cotangent homology,
and finite-span conclusion are all explicit. Its source is the differential-basis paragraph
of Stacks Tag 07FG. Its plan uses the existing middle-exactness Mathlib leaf and universal
differentials, so it does not reintroduce the full homology-sequence module.

Edge cases checked mathematically before stating it: for I = 0 take D = 0 and f empty;
for theta = 0 the same choices work; for k = K, use theta transported to K, with f empty,
since the section and structure-map scalar actions coincide on I. For a finite purely
inseparable field extension, the exceptional differential directions belong to the finite
kernel and are retained in f. Infinite p-bases are allowed: only the kernel's finite basis
has finite coordinate support, not the full module of differentials. The statement needs
no finite dimensionality of I, Lambda, or either absolute differential module.

## Second reading by T1

1. Compared the submitted coefficient-correction module with the repository version. The
   existing theorem signature, hypotheses, conclusion, namespace, and visibility are
   byte-for-byte unchanged; only a proof and a proof-only import were added. The new
   derivation module is separately declared and does not alter existing declarations.
   Verdict: passed.

2. Compiled both delivered modules with `lcompile.py`, including the sandbox import order.
   The only remaining `sorry` is the named theorem
   `Algebra.exists_finite_rank_defect_derivation`; it has a public docstring, source, and
   matching DAG node. No forbidden commands or hollow definitions occur. The upper theorem
   consequently depends on `sorryAx` through this explicitly split theorem. Verdict: passed.

3. Checked the split-off theorem against the coefficient-correction proof: it is strictly
   smaller, omits the coefficient closure and section conclusion, and supplies only the
   finite-rank derivation data actually consumed. Its hypotheses and conclusion are
   mathematically meaningful in zero-ideal, zero-derivation, and scalar-extension edge
   cases. Searches recorded in the report found no existing Mathlib or library duplicate.
   Verdict: passed.

4. Checked pruning and route. The proof uses the new finite-rank derivation theorem and
   Mathlib Jacobi--Zariski support inside that theorem; it does not use the previously
   imported full homology-sequence route. The coefficient-correction node records the new
   proof dependencies and the unit route remains realized. Verdict: passed.

5. Checked DAG/Lean agreement. The changed node's proof steps and `proof_deps` describe the
   actual discrepancy calculation, finite-rank theorem application, endomorphism, and
   closure argument. The new node's Lean statement matches its theorem declaration and
   includes source, proof plan, searches, and creation metadata. Verdict: passed.

Changed during second reading: added this required review section only; no Lean code,
statements, definitions, imports, or DAG records were altered.
