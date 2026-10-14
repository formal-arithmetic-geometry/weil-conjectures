## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.tensorGradedCoefficient_sheaf_action`
without changing its statement or either existing definition. Added proof-only imports
of `TensorCoefficientActionSupport` and `TensorCoefficientActionOnSummand`.
The proof tests on the coproduct injections, uses the one-summand tensor formula
on the contributing degree, and kills all other degrees by support and orthogonality.
Both new statements are sheaf morphism statements, with no cohomology calculation.
Updated the original node's proof route. All three modules compile without warnings.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.tensorGradedCoefficient_sheaf_action`.
There are no remaining sorries in the assigned module.
Added two holes, so this is a decomposition, not a completed proof of the local
sheaf calculations (holes closed: 1; holes added: 2; net: -1).

- `AlgebraicGeometry.Scheme.Modules.tensorGradedCoefficient_action_support`:
  `lem-sc-tensor-coefficient-action-support`.
- `AlgebraicGeometry.Scheme.Modules.tensorGradedCoefficient_action_on_summand`:
  `lem-sc-tensor-coefficient-action-on-summand`.

Each is exactly `by sorry` in its own module with a source and proof in words.
The support lemma only gives the degree of the action. The other lemma only
computes the action on one source summand. Neither asserts the final equality on I.
The combining proof handles n=0 by natural-number cancellation and does not assume
positive degree, a nonzero section, or an affine scheme. The new statements also
allow e=0, d=0, the zero ideal, and f=0; the local formulas still apply.

## No longer needed

No imports removed and no existing dependency modules pruned. Of the old direct proof dependencies,
`lem-weil-pbc-closed-immersion-unit-quotient` and
`lem-sc-square-zero-ideal-tensor-unit` are no longer direct dependencies of the
combining proof: the two new local-calculation nodes use them. They remain
transitively needed, so neither node nor module is pruned.
`lem-sc-square-zero-tensor-graded-presentation` remains a direct dependency.
The product theorem `tensorGradedSection_product` is not used; its module remains
publicly imported because it defines `tensorGradedSection` used by the statement.

## Where the brief, the DAG or earlier work was wrong

The original plan compresses the two local sheaf calculations into one step;
the cited declarations supply the presentation and comparison constructions but
do not state either compatibility. These are now separate, strictly partial
statements with the categorical combination proved in Lean.
No statement correction or forced adaptation was needed.

Read Stacks coherent.tex, lemma-ample-on-reduction, equation-ses and the following
graded direct-sum sequence; read cohomology.tex,
lemma-boundary-derivation-over-cup-product, especially its first proof paragraph.
These literature files are absent from this checkout, so copies were fetched into
the sandbox scratchpad from the Stacks project's source repository.
The unit's realized statement and steps remain untouched.
Searches: LeanFinder returned graded ring and cotangent lemmas, none with the
required sheaf comparison; Loogle found IsColimit.hom_ext; grep found no existing
comparison names in Mathlib; LeanSearch returned HTTP Internal Server Error.
Repository and blueprint searches found no existing statement for either new lemma.

## New nodes

`lem-sc-tensor-coefficient-action-support`, module
`Sheaf.AlgebraicGeometry.TensorCoefficientActionSupport`: factors the action on an
arbitrary degree-d injection through the degree-(n+d) injection. This leaves the
local lifting and gluing argument for its next worker.

`lem-sc-tensor-coefficient-action-on-summand`, module
`Sheaf.AlgebraicGeometry.TensorCoefficientActionOnSummand`: computes the action on
the single relevant source summand with the explicit canonical tensor transports.
It leaves the local multiplication and comparison coherence for its next worker.
No change records are needed.


## Second reading by M3

1. Compared the assigned module with the repository using diff. The only changes
   are two plain proof imports and the original theorem's proof body. Both existing
   definitions, every existing signature, visibility and docstring are byte-for-byte
   unchanged. No interface change or change record is required. Verdict: pass.
2. Compiled all three modules locally in import order, without errors or warnings.
   Scanned all delivered Lean files: exactly the two reported named theorem holes,
   each exactly `by sorry`; no forbidden declaration or hollow definition. A scratch
   copy printed axioms for both definitions, the original theorem and both new
   theorems. The definitions use only propext, Classical.choice and Quot.sound;
   the theorems additionally use sorryAx from the reported unresolved statements.
   The scratch copy was removed. Verdict: pass as a decomposition, not a completed
   proof of the sheaf calculation.
3. Read both new statements and their full docstring arguments against the graded
   presentation fields, canonical boundary comparisons, and the cited paragraphs
   of coherent.tex and cohomology.tex. Degree support follows from a local degree-n
   lift, b_multiply, and the kernel equation; squareZero makes it independent of the
   lift. The one-summand formula uses the canonical comparisons fixed by the unit
   and kernel inclusion and gives precisely tensor multiplication. Checked n=0,
   d=0, e=0, f=0 and zero ideal: no degree cancellation assumes n positive; unit
   transports handle zero powers; the zero cases give zero maps. Neither statement
   restates the complete projection equality: one only gives support, the other
   only computes a single input summand. Each has its node and source. Independent
   LeanFinder search for a square-zero quotient action on direct-sum components
   returned TrivSqZeroExt multiplication lemmas, not this sheaf comparison. Loogle
   found Cofan.IsColimit.hom_ext, already used. Mathlib grep for quotient/tensor
   action ingredients found adjunction unit uniqueness; repository searches found
   mulTensorPowSection_app and related section formulas, but no existing proof of
   either new sheaf-level compatibility. These ingredients do not close either
   local lifting/gluing calculation in a few minutes. Verdict: pass.
4. Read the proof from the original theorem downward. Coproduct extensionality,
   the diagonal formula and orthogonal projections give the stated result; omega
   uses n+d=n(e+2) only to cancel addition. All imports are needed: the public
   product-projection module supplies tensorGradedSection in the signature, and
   both added imports are plain proof imports. The unused product theorem is not
   invoked. Read sk-thm-curveestimate.json: its realized statement remains
   thm-sc-proper-cohomology, with no realized steps changed or bypassed. No module
   becomes unreachable. Corrected the pruning report to explicitly distinguish
   the two old direct dependencies now used transitively through the new nodes.
   Verdict: pass.
5. Compared the existing node with the repository: only proof, proof_deps and
   proof_origin differ. Checked each of the three node Lean statements verbatim
   against its module and checked proof_deps equals the union of proof-step uses.
   The two new nodes include their complete statements, sources, proofs, searches,
   creation and blueprint records, chapter/unit and Lean records. Their routes
   retain the three original local-calculation dependencies. Verdict: pass.

Second reading changed only report.md: completed the direct-dependency pruning
account and added this review. No Lean proof, statement, definition or node repair
was needed. Holes closed: 1 original; holes added: 2; net: -1 (decomposition).
