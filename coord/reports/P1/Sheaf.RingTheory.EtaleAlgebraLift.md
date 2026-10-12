## What changed
Added two proof-only component imports to `Sheaf.RingTheory.EtaleAlgebraLift`.
Its conjunction theorem combines the strictly smaller etaleness/finite-presentation and
specified-reduction-isomorphism components. The existence theorem now obtains an upstream
square Jacobian presentation, reindexes it by `Fin (Nat.card iota)`, lifts each relation by
`MvPolynomial.map_surjective`, constructs `CoefficientLift` from those polynomials and their
proved reduction equalities, and applies the conjunction theorem. Existing signatures,
visibility, definitions, and public imports are unchanged.

## Proved and sorry left
Closed the original proof holes:
- `Algebra.SquareJacobianPresentation.CoefficientLift.etale_and_reduction_equiv`.
- `Algebra.exists_etale_coefficientLift`.

Added and left the component holes:
- `Algebra.coefficientLift_etale_fp`, node `lem-exc-etale-algebra-lift-etale-fp`.
- `Algebra.coefficientLift_reduction_equiv`, node `lem-exc-etale-algebra-lift-reduction`.

No sorry remains in the item module. Both original results still depend on the component
sorries; this is a decomposition, not an axiom-free proof. Two holes closed minus two added
is net zero for this delivery, subject to the maintainer's pinned-baseline ledger.
The imported existing `CoefficientLift.liftIdeal_vanish` is also still open and is unchanged.

## No longer needed
No old proof-dependency node or existing import is pruned: the construction and square
Jacobian characterization remain used, now including the proved existence reduction.
Removed the first worker's unused proof-only
`WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree` import from the new
`EtaleAlgebraLiftEtaleFP` module. That module import remains necessary in the item for the
existence proof. No module is claimed as pruned.

## Where the brief, the DAG or earlier work was wrong
The first worker left the existing parent node's proof route unchanged even though its proof
now uses new components; corrected `proof`, `proof_deps`, and `proof_origin` to match Lean.
The first worker did not close the straightforward existence reduction. Its new proof
summaries were too terse, and its search records were not backed by this sandbox's search
log; expanded the summaries and ran independent recorded searches. LeanSearch returned an
internal-server error, which is recorded as unavailable without a no-match verdict.

## New nodes
`lem-exc-etale-algebra-lift-etale-fp` isolates the block Jacobian determinant/unit calculation
and its application to the square Jacobian criterion. It is strictly part of the original
argument and does not assert a reduction isomorphism.

`lem-exc-etale-algebra-lift-reduction` isolates compatibility and invertibility of the specified
reduction map. It is strictly part of the original argument and does not assert etaleness.
Each has a new module, its unchanged Lean signature, explicit source, expanded natural-language
proof, dependency records, and independent search records. No change record is required:
there is no changed existing interface or definition.

## Second reading by P1
1. PASS: compared the item with the repository using diff and checked each existing theorem's
   signature byte for byte up to `:=`; both are identical. The other modules are new.
   No existing data or visibility changes and no undeclared interface change.
2. PASS: all three delivered modules compile locally in import order without warnings.
   A scratch import file printed axioms for both original theorems and both new components:
   only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. Text inspection found
   exactly the two reported, whole-proof, public named theorem sorries, and no forbidden
   declarations or hollow definitions. The scratch file was removed before delivery.
3. PASS as a decomposition: components are the two independent strict parts of the existing
   proof, not renamed copies of the whole statement. Reviewed m = 0 (empty determinant 1,
   auxiliary relation t - 1), zero rings, I = bottom, and I = top; no nontriviality or proper-
   ideal assumption is needed. The reduction argument uses P's full presentation property,
   not just vanishing equations. Searched by leanfinder, loogle, recorded grep and rg in
   both library roots. Related first-isomorphism and polynomial quotient equivalences do
   not supply the specific coefficient-lift theorem; upstream standard-etale lifting
   treats a different presentation and does not replace either component directly.
4. PASS: the item applies the component statements from the top down, and the existence proof
   uses the already proved upstream characterization, reindexing, and polynomial-map
   surjectivity. Imports are minimal for the supplied proofs; no original proof-dependency
   node is omitted from the pruning report. Read the unit record: its existing realized
   statement and step lists are empty and remain unchanged. The open-closed unit route is
   preserved; this refinement is below that route.
5. PASS after repair: the existing node's proof and dependency union now describe the two
   components and the existence construction. New nodes match their Lean declarations,
   source, chapter/unit, strictly smaller argument, and dependencies. Their statement
   dependency references and search records were repaired. No target or unit record changes.

Second reading changed: closed `Algebra.exists_etale_coefficientLift`; expanded both component
proof docstrings; removed the unused new-module proof import; repaired parent proof metadata,
new-node dependency references and recorded searches; corrected the decomposition accounting.
