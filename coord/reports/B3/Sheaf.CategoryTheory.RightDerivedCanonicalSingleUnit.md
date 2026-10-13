## What changed

Replaced the first worker's coefficient-precomposition restatement with
`Sheaf.CategoryTheory.RightDerivedCanonicalSingleUnitShift`. Its named theorem
isolates transport of the additive derived unit from degree n to degree zero,
before the classical derived-functor comparison and before using left exactness.
The original theorem now expands the comparison, applies that transport, invokes
`rightDerivedPlusSingleUnitHomology_comp_comparison`, and cancels the classical
augmentation using Mathlib's `rightDerivedZeroIsoSelf_inv_hom_id_app`.
The new import in the original module is private. Existing signatures and definitions
are unchanged. Updated the original DAG proof and added the shift-transport node.

## Proved and sorry left

Closed the original syntactic hole
`CategoryTheory.Functor.rightDerivedFunctorPlusUnit_canonical_single`
(node `lem-pc-right-derived-canonical-single-unit`) by a complete reduction.
Added one hole:
`CategoryTheory.Functor.rightDerivedFunctorPlusUnit_canonical_single_shift`
(node `lem-pc-right-derived-canonical-single-unit-shift`). It is the sole `sorry`
of the delivered files, in a named theorem with a source and proof docstring.
This is a decomposition: one hole closed, one added, net zero. The original
statement is not yet proved without `sorryAx`. The shift calculation could not
be closed in a few minutes; it requires expanding the coherent single, quotient,
unit and homology shift comparisons.

## No longer needed

Removed the undelivered `RightDerivedCanonicalSingleUnitPrecomp` module and its
undelivered node `lem-pc-right-derived-canonical-single-unit-precomp`.
No existing library module is pruned. The old proof dependency
`lem-sp-derived-functor-single-identification` is no longer a direct dependency
of this node's reduction; its upstream comparison remains reachable through
`RightDerivedSingleDegreeComparison`. The other two old proof dependencies are
used. The original public comparison import is needed by the statement, and the
original private single-unit comparison import is used by the proof.
No unit-level route or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The first worker's new theorem was equivalent to the whole item by cancellation
of an isomorphism, rather than a strict part of its proof. Its node's prose also
stated the original equation instead of its actual precomposed signature, and
it did not update the original node to reflect the proposed proof. Those faults
are repaired. The first report incorrectly described two public imports; the
original module has one public statement import and one private proof import.
Stacks Tag 015J remark (1) supplies the single-object context, while the actual
canonical shift normalization is agent-written from the proved upstream
`commShift_rightDerivedFunctorPlusUnit`, not stated verbatim in that source.

## New nodes

`lem-pc-right-derived-canonical-single-unit-shift`, in
`lean/Sheaf/CategoryTheory/RightDerivedCanonicalSingleUnitShift.lean`, is the
additive shift-transport step. It requires enough injectives, not Grothendieckness
or left exactness, and ends at the degree-zero unit rather than at the final
coefficient identity. No change records are needed.

## Second reading by B3

1. Compared the original module with the repository: the existing declaration
   signature, hypotheses, docstring and definitions are byte for byte unchanged.
   Only its proof and one private import changed. No other existing module changed.
2. Compiled both files with `lcompile.py --all`, without errors or warnings.
   Scanned for forbidden declarations and definition holes: none. Scratch
   `#print axioms` checks show only `propext`, `Classical.choice`, `Quot.sound`
   and the remaining `sorryAx` on the original theorem and shift lemma. The used
   degree-zero unit comparison has only the three allowed axioms.
3. Rejected the equivalent precomposition split. The replacement is precisely
   the unit shift-transport step; the classical comparison and augmentation
   cancellation are proved in the original module. Read its weaker assumptions
   and checked n=0 via shift-unit coherence, and zero coefficients via zero maps;
   neither requires extra hypotheses. Its source, proof docstring, signature and
   node agree. Searched with LeanFinder, Loogle, LeanSearch (unavailable), source
   grep and project/DAG searches using shift/unit vocabulary; found supporting
   shift lemmas, but no existing theorem of this transport equation.
4. The reduction explicitly uses the existing proved degree-zero comparison and
   Mathlib cancellation. Both existing imports are necessary; the helper publicly
   imports only the module whose degree-zero unit definition its statement uses.
   Listed every removed direct dependency above. The assigned unit's realized
   statement and step arrays are empty; they were inspected and left unchanged.
5. Updated the original node's proof, proof_deps and proof_origin to match the
   Lean reduction. The new node has all required fields, the exact Lean signature,
   genuine recorded searches and the additive shift-normalization proof.

Changes made in this second reading: removed the precomposition restatement,
introduced the shift-only obligation, proved the classical comparison and
augmentation cancellation, corrected the DAG and rewrote the report to describe
one decomposition with net zero rather than a proof without holes.
