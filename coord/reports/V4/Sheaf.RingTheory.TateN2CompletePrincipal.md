## What changed

Replaced the first worker's two unproved characteristic-case restatements with a real
reduction in `Sheaf.RingTheory.TateN2CompletePrincipal`. The characteristic-zero branch
uses Mathlib's `IsIntegralClosure.finite` directly. The positive-characteristic branch
uses the already proved `isN2_of_finite_purelyInseparable_integralClosure`, an explicitly
proved private separatedness helper, the new closed-fibre lemma, and the existing
`Module.finite_and_span_eq_top_of_adicComplete`.

The only new public statement is in its own module
`Sheaf.RingTheory.TatePurelyInseparableClosureQuotientFinite`: for a fixed finite purely
inseparable extension, its integral closure modulo x is finite over R/xR. This conclusion
is only the closed-fibre part of Tate's argument and does not assume completeness.
The original public signature is byte for byte unchanged; all original public imports
are unchanged. Added imports in the original module are proof-only.

## Proved and sorry left

Closed the original hole `tate_n2_complete_principal`, conditionally on the new named hole.
The private helper `closure_hausdorff` is fully proved and uses only propext,
Classical.choice, and Quot.sound. The characteristic-zero branch is fully proved.

Added one hole: `tate_purely_inseparable_closure_quotient_finite`, node
`lem-weil-pbc-tate-purely-inseparable-closure-quotient-finite`.
No sorry remains in the item module. The two first-worker holes
`tate_n2_complete_principal_char_zero` and `tate_n2_complete_principal_char_p` and their
new node files were removed before delivery; they were never part of the baseline.
This is a decomposition: one original hole closed, one new hole added, net zero.
The main theorem's axioms include sorryAx through the named closed-fibre hole.
The existing purely-inseparable criterion and complete-module theorem have no local
holes added by this delivery.

## No longer needed

Removed the item's proof-only import `Sheaf.FieldTheory.SeparableExtension`:
characteristic-zero separability is provided directly by Mathlib instances.
Removed the direct import `Sheaf.RingTheory.DimOneResidueFieldsFinite` from the item;
it remains imported by the new closed-fibre module for that node's proof plan.
No claim is made that the latter module is pruned from the targets' closure.

Every old proof dependency absent from the item's new direct proof_deps is listed below.
Those transferred to the closed-fibre lemma remain needed transitively:

- `def-weil-algebraic-closure` (transferred to the closed-fibre proof plan).
- `def-weil-finitely-generated-module` (transferred to the closed-fibre proof plan).
- `def-weil-pbc-integral-closure` (transferred to the closed-fibre proof plan).
- `def-weil-pbc-krull-dimension-ring` (transferred to the closed-fibre proof plan).
- `def-weil-pbc-localization-at-prime` (transferred to the closed-fibre proof plan).
- `def-weil-ring-frobenius` (transferred to the closed-fibre proof plan).
- `lem-weil-pbc-algebraic-generators-finite-extension` (transferred to the closed-fibre proof plan).
- `lem-weil-pbc-dim-one-residue-field-extensions-finite` (transferred to the closed-fibre proof plan).
- `lem-weil-pbc-field-degree-multiplicativity` (transferred to the closed-fibre proof plan).
- `lem-weil-pbc-finite-module-over-finite-algebra` (transferred to the closed-fibre proof plan).
- `lem-weil-pbc-integral-closure-finite-extension-normal` (transferred to the closed-fibre proof plan).
- `lem-weil-pbc-localization-dimension-chains-below-prime` (transferred to the closed-fibre proof plan).
- `lem-weil-pbc-localization-noetherian` (transferred to the closed-fibre proof plan).
- `lem-weil-pbc-module-finite-extension-of-finite` (transferred to the closed-fibre proof plan).
- `lem-weil-pbc-noetherian-height-quotient-bound` (transferred to the closed-fibre proof plan).
- `lem-weil-pbc-noetherian-submodule-finite` (transferred to the closed-fibre proof plan).
- `lem-weil-pbc-prime-residue-field-algebra` (transferred to the closed-fibre proof plan).

Those no longer used by either the reduction or the closed-fibre plan:

- `def-weil-pbc-separable-algebraic-extension`.
- `def-weil-pbc-separable-field-extension`.
- `def-weil-pbc-transcendence-basis`.
- `lem-weil-pbc-char-zero-field-extension-separable`.

## Where the brief, the DAG or earlier work was wrong

The first worker's new nodes copied the original statement without their characteristic
hypotheses, carried empty proof plans, and recorded inherited searches rather than new
searches. Their declarations had no proof docstrings, and the item's existing node was
not updated. Splitting off the positive-characteristic N-2 conclusion also left the core
argument under a different name. These faults were repaired rather than delivered.

The old characteristic-zero plan unnecessarily passed through the library's
separably-generated-extension definition and a transcendence basis. Mathlib already
provides separability of finite extensions in characteristic zero.

The Stacks source is https://stacks.math.columbia.edu/tag/032P (lemma-tate-japanese),
read online because the cited local algebra.tex is absent on this machine. Its proof
indeed establishes closed-fibre finiteness before using completeness to obtain total
finiteness. The proof of the new lemma explicitly supplies the injection S/xS into
T/xT after enlarging L, so finiteness descends at the quotient level.

## New nodes

`lem-weil-pbc-tate-purely-inseparable-closure-quotient-finite` states precisely the
closed-fibre finiteness result, with no completeness assumption. Its docstring gives
the full argument, including x=0, enlargement, the prime yT, residue-field finiteness,
N-2 of the quotient, filtration, and the injection needed to undo enlargement.
LeanFinder, Loogle, and Mathlib source grep were actually run with alternative terms;
none supplied this result. LeanSearch returned Internal Server Error and is recorded
as unavailable. No statement or definition change record is needed.

## Second reading by V4

1. Compared the delivered item against the repository with diff. Extracted and compared
   the existing theorem signature: byte for byte identical, including universes,
   normality, quotient-domain hypothesis, adic completeness, and N-2 of the quotient.
   No definition was changed; the original public imports are unchanged. Verdict: pass.
2. Compiled both modules in import order using lcompile.py. No errors or warnings.
   Scanned for forbidden declarations and hidden sorry: only the one named theorem in
   the new module has sorry, with a matching node and full proof docstring. Printed
   axioms of the private helper, the main theorem, and the new theorem. The helper has
   only propext, Classical.choice, Quot.sound; the latter two additionally have sorryAx.
   No construction chooses an arbitrary object from an unproved existence theorem.
   Verdict: pass as a conditional decomposition, not an unconditional proof.
3. Read Tag 032P and checked the new statement against the argument before Tag 031D.
   Checked x=0 (quotient is R; N-2 applies), L=K (normal closure is R), and q=1
   (filtration has one factor). If x is a unit the quotient-domain hypothesis rules it
   out; the zero ring is excluded by IsDomain. For x nonzero, normality gives
   S intersect xT = xS, which is necessary for descent after adjoining the root.
   Checked that residue-field finiteness is used only after localizing a Noetherian
   domain at the nonzero prime principal ideal, whose dimension is one. The quotient
   ring is Noetherian, so its submodule finiteness argument applies. S/xS is killed by x,
   making R-module finiteness equivalent to R/xR-module finiteness. Searched Mathlib,
   repository RingTheory, and upstream RingTheory for alternative closure/quotient and
   Hausdorff terms. No existing declaration gives this closed-fibre statement.
   Verdict: true, needed, strictly less than the item; documentation and node match.
4. Checked the top-down route: direct Mathlib finiteness in characteristic zero; the
   existing purely-inseparable criterion in characteristic p; direct Frobenius-power
   separatedness; then closed-fibre finiteness and the existing complete-module theorem.
   Reviewed every imported dependency's relevant declaration. The unit sk-thm-p1's
   realized statement and four step lists do not name this item; they are unchanged.
   Its ancestor's use of Tate in the complete-local-Nagata reduction is retained.
   All old dependencies no longer used directly are accounted for above; dependencies
   of the residual closed-fibre lemma are not claimed as globally pruned. Verdict: pass.
5. Updated the existing item's proof, proof_deps, and proof_origin to the written Lean
   reduction. Replaced the first worker's two incomplete nodes with one complete node:
   self-contained statement, actual searches, source, proof steps and their union,
   blueprint ancestry, chapter/unit, created record, and verbatim Lean signature.
   The new proof plan follows the original steps 4-10 and includes quotient descent.
   Verdict: pass.

Second reading changed: removed both characteristic-case holes and their node files;
proved the zero-characteristic branch and separatedness; replaced the positive case
with the purely-inseparable/closed-fibre/complete-module reduction; added the single
closed-fibre module and node; corrected dependency records, imports, and this report.
