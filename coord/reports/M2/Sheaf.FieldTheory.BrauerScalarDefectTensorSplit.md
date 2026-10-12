## What changed

Preserved the signature and docstring of
Field.tensor_opposite_split_of_brauerScalarDefect_eq. Replaced its sorry with a complete
Lean reduction following the original three-step descent plan. Added proof-only imports
of BrauerScalarDefectTensorLifts, GaloisUnitsScalarCoboundary, and GaloisMatrixCocycleSplit.
The main proof constructs the rescaled lifts, proves their genuine cocycle equation by
centrality and unit cancellation, and proves that scalar rescaling preserves conjugation.
The original matrix size and its nonzero proof are retained.

Added three new modules, each with one public theorem and its own DAG node. The scalar
coboundary theorem is proved: the private exists_homogeneous_boundary helper constructs
concrete kernel/cokernel homology data and extracts a homogeneous boundary from equality
of class projections. Evaluation at (1,g), homogeneous equivariance, the differential,
and multiplicative translation give the correctly signed scalar ratio. No arbitrary data
are chosen in definitions. Updated the item's proof, proof_deps, and proof_origin to match.

## Proved and sorry left

Closed the original hole Field.tensor_opposite_split_of_brauerScalarDefect_eq
(lem-sc-brauer-scalar-defect-tensor-split) by decomposition; its module has no sorry.
Also proved Field.exists_scalar_cochain_of_galoisUnits_class_eq
(lem-sc-galois-units-scalar-coboundary), including its private homogeneous-boundary helper,
without sorry dependencies.

Added exactly two holes, each the whole proof of its named public theorem:
- Field.exists_tensor_opposite_scalarDefect_lifts
  (lem-sc-brauer-scalar-defect-tensor-lifts), in BrauerScalarDefectTensorLifts.
- Field.nonempty_algEquiv_matrix_of_galois_cocycle
  (lem-sc-galois-matrix-cocycle-split), in GaloisMatrixCocycleSplit.

This is a decomposition, not an axiom-free completion: one original hole closed, two holes
added, net minus one pending the ledger's import-closure computation. Each remaining
statement is strictly one part of the original argument. Tensor lifts require no equality
of cohomology classes and produce only a separable-closure splitting. Matrix descent
requires already genuine cocycle data and mentions neither CSAs nor scalar defects.
Neither auxiliary restates the original theorem or uses downstream Brauer equivalence.

Edge cases checked in the mathematical statements: scalar coboundaries need no normalized
representatives (the sign comes from z-w); tensor sizes multiply nonzero sizes; descent
works for split algebras, trivial cocycles, arbitrary characteristic (averaging divides by
no group order), and n=0, where existence of e forces the zero algebra.

## No longer needed

Removed the redundant direct proof import Sheaf.FieldTheory.GaloisUnitsCohomology:
the unchanged public import BrauerScalarDefect already supplies the statement definitions.
The new generic matrix-descent module also imports only the Mathlib field, matrix,
tensor and local-constancy APIs, and does not import BrauerScalarDefect or continuous
cohomology. The scalar-defect and cohomology definition nodes remain necessary statement
dependencies of the item; no mathematical node or
module is claimed pruned from the targets' closure.

The archived earlier-attempt backward/equivalence auxiliaries are unused. No imports of
BrauerScalarDefectFaithfulBackward, BrauerScalarDefectBackward, or
BrauerEquivalentTensorSplit are added. Earlier sandbox copies of the unchanged definition
modules and a stray duplicate item file were archived outside lean/ before compilation.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan has only definition dependencies; the tensor lift construction and
matrix descent were substantive unrecorded steps. They now have independent statements,
complete proof descriptions and nodes. The existing homogeneous comparison theorem only
asserts existence of an abstract equivalence and does not expose compatibility with the
particular cocycle projections needed here; the new scalar lemma proves that compatibility
directly with Mathlib's concrete homology API.

The earlier proposal duplicated the downstream backward theorem and transferred the
entire unresolved descent to it. This delivery avoids that cycle and equivalence restatement.
LeanSearch was unavailable (recorded service errors); LeanFinder and source searches ran.
The unit sk-thm-br statement and its route are unchanged; its realized lists are empty,
and this reduction remains within the original field Brauer comparison descent argument.

## New nodes

lem-sc-brauer-scalar-defect-tensor-lifts: tensor/opposite splitting over the separable
closure with quotient projective defect, in BrauerScalarDefectTensorLifts; sorry left.

lem-sc-galois-units-scalar-coboundary: locally constant scalar cochain from equal
homogeneous cohomology projections, in GaloisUnitsScalarCoboundary; fully proved.

lem-sc-galois-matrix-cocycle-split: genuine locally constant matrix cocycle descends a
split algebra, in GaloisMatrixCocycleSplit; sorry left. Its proof expands matrix Hilbert 90
using Artin independence and invariant averaged vectors, and then restricts fixed entries.

Validation: all four modules compile without warnings through lcompile --all. The delivery
dry run passes static checks and declaration/axiom probes; its sole deferred check is
the second reading, which belongs to the next worker. Nothing was pushed.

No change records or forced adaptations: all existing signatures, visibility, definitions,
and public imports remain unchanged. The three new modules are imported only by the proof.

## Second reading by M2

1. **Interfaces and statements.** Compared the delivered item module byte-for-byte with the repository version: the theorem signature and all existing declarations are unchanged; the three auxiliary declarations are new and their node statements match their Lean types. Verdict: pass.
2. **Proof and axioms.** Compiled all four delivered modules with `lcompile.py --all`; there are no forbidden commands and no `sorry` in the item or in the scalar-coboundary proof. The two intentionally split declarations contain the only remaining `sorry`s, each named in the report and represented by a node. The proved item depends on `sorryAx` only through those explicitly split imported theorems; no additional axiom is introduced. Verdict: pass.
3. **New statements.** Checked the tensor-lift and matrix-descent statements are strict substeps of the target, while the scalar cochain theorem supplies exactly the missing rescaling datum. Their docstrings give the source and proof route; no duplicate declaration was found in the repository. Verdict: pass.
4. **Pruning and route.** The proof uses the three new proof-only imports and retains the original public definition import; the removed direct cohomology import is unnecessary. The DAG `proof` and `proof_deps` agree with the proof, and no old proof-dependency node is silently bypassed. Verdict: pass.
5. **Unit and DAG consistency.** The `sk-thm-br` unit has no realized Lean statement or steps, so this field-theory reduction does not bypass a realized unit route. New nodes carry chapter, unit, source, proof, and Lean records, and the report records the two split holes. Verdict: pass.

Changed after reading: added this second-reading section only; no Lean code, node statement, or definition required repair.
