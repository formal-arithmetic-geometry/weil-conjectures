## What changed

Proved `HomologicalComplex₂.coneHorizontal_projection_kernel` in
`Sheaf.Algebra.Homology.ConeHorizontalProjectionKernel` without changing its signature,
visibility, existing docstring, or imports. Added proved private helpers for column insertion,
projection on generators, generator factorization, and signed source/target reconstruction.
The proof sends the p-tail into the next tail under `1 - projection ≫ insertion`, and
uses this on the kernel arrow to prove the reverse inclusion. The forward inclusion follows
from vanishing on every next-tail generator. Updated the node's proof and proof_origin to
record this implemented route. No other module is adapted.

## Proved and sorry left

Closed the one original hole:
`HomologicalComplex₂.coneHorizontal_projection_kernel`
(node `lem-sp-cone-horizontal-projection-kernel`). No holes remain in the item, and no
holes were added or split off. All private helpers are proved. Compilation succeeds without
warnings through `lcompile.py`; the delivery dry run provides the declaration axiom probe.

## No longer needed

None of the three original imports can be removed: they supply the projection, explicit
tails, and degreewise filtration notation in the unchanged statement. No dependency module
is pruned. The planned abstract finite-biproduct kernel calculation is unnecessary: the
proof instead constructs the insertion and proves the defect factorization on generators.
The theorem `coneHorizontal_step_stable` itself is not used; its module remains necessary
for the real definitions `coneHorizontalSummand`, `coneHorizontalImage`, and
`coneHorizontalStep`. No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The numbered DAG steps are a valid plan,
but their abstract sub-biproduct identifications are unnecessary for this proof. The local
`coord/delivery-errors.md` has sections A–H and no section I. The cited unit record has empty
realized statement/step lists; the present proof keeps the same definition dependencies.
Negative degrees and out-of-diagonal indices are handled explicitly by the zero summand
calculations; the source sign is checked by `((-1)^p)^2 = 1`.

## Second reading by V2

1. Compared the delivered module with the repository version. The theorem signature, visibility,
   docstring, and public imports are byte-for-byte unchanged; only private proof helpers and the
   proof body were added.
2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings. The axiom probe
   shows only the permitted axioms for the proved declarations. There are no `sorry`, `axiom`,
   `unsafe`, `opaque`, `extern`, or `implemented_by` declarations.
3. Read the proof and checked edge cases handled by the explicit branches (negative degrees,
   invalid diagonal indices, and the boundary column). The projection and reconstruction lemmas
   establish the stated kernel equality with the required signs. No split-off statements or new
   nodes were added, and no existing declaration is duplicated.
4. Checked the proof route against the node and imports. It uses explicit cone generators, the
   filtration step identification, and the defect endomorphism without bypassing a realized unit
   step. All three public imports are used by the statement or proof, so none can be pruned. The
   DAG proof and `proof_deps` match the implemented route.
5. The target statement is unchanged and remains exactly the node statement. The unit record has
   no realized entries to update, and no definition or interface change requires a change record.

Changed nothing during second reading beyond this report section; the delivered proof is accepted.
