## What changed

Proved `Field.exists_brauerScalarDefect_lifts` from two smaller steps, preserving its
signature and its public imports. Added proof-only imports of the two new modules:
`Sheaf.FieldTheory.BrauerScalarDefectLifts` and
`Sheaf.FieldTheory.BrauerScalarDefectCocycle`.

The first step, `Field.exists_locallyConstant_brauer_lift`, is completely proved.
A finite K-basis of A determines a finite tuple of Galois-transformed matrix entries.
Their stabilizers are open by Mathlib's `stabilizer_isOpen_of_isIntegral`.
`continuousSMul_iff_stabilizer_isOpen` and `LocallyConstant.unflip` make the tuple
locally constant. Choose one automorphism for each tuple in its actual range, then
use the proved `Algebra.IsCentral.exists_unit_map_eq_conj` for that representative.
The chosen inverse unit is constant on each tuple fiber. Equality on the basis
transports its conjugation identity to every automorphism with that tuple.
All the choices in this proof come from proved existence statements.

The second step isolates the continuous scalar cocycle construction for given
locally constant lifts. Its docstring includes centrality, the cocycle calculation,
continuity, homogeneous coordinates, and the passage to Mathlib's cycles object.
The parent now combines the two steps with a complete Lean proof.

The three modules compile cleanly with the prescribed lcompile tool. The original
unit route is retained; `sk-thm-br` has no realized step at this subsidiary node.

## Proved and sorry left

Closed the original hole `Field.exists_brauerScalarDefect_lifts` (node
`lem-sc-brauer-scalar-defect-exists`). The item's module has no `sorry` left.

Also proved `Field.exists_locallyConstant_brauer_lift` (new node
`lem-sc-brauer-scalar-defect-lifts`) without `sorry`.

Added one hole: `Field.exists_brauerScalarDefect_cocycle` (new node
`lem-sc-brauer-scalar-defect-cocycle`). This accepts fixed locally constant lifts
and proves only existence of their continuous homogeneous scalar-defect cocycle;
it does not construct the lifts or repeat the original existential statement.
One original hole closed and one strictly smaller hole added: a decomposition,
with the lift-construction step proved, rather than a complete unconditional proof
of the parent theorem. Net hole reduction is zero before import-closure accounting.

## No longer needed

No imports or existing DAG nodes are removed. The original proof's finite Galois
extension construction is unnecessary for the proved lift step: the finite basis
and open stabilizers suffice. There was no separate node or import for that step.
The scalar-defect definition and continuous Galois units representation remain used.

## Where the brief, the DAG or earlier work was wrong

The original node had one large prose step and only the scalar-defect definition
as its proof dependency; no stated construction theorem existed to apply.
Its lift step can be proved directly from the existing ReducedNorm module and
Mathlib. The cocycle step is now a precise separate interface with the essential
local-constancy hypothesis explicitly present.

Checked the source in `etale-cohomology.tex`, `lemma-central-simple-algebra-pgln`
and `equation-two-cocycle` before `theorem-brauer-delta`, corresponding to 03R6/03R7.
The chosen conjugation and scalar-defect orientation is the original Lean statement's.
The new nodes retain that orientation; no target or existing statement was changed.

Edge cases: positive n permits extraction of the scalar from a diagonal entry;
n=0 is excluded as in the original theorem. For n=1 the defect is the ordinary
scalar coboundary. Neither b(1)=1 nor normalization is assumed or needed. The
arguments use separable-closure units and also apply in positive characteristic
and over imperfect fields. Local constancy of b is necessary in the cocycle
interface and is supplied by the proved lift theorem.

## New nodes

`lem-sc-brauer-scalar-defect-lifts`, in
`lean/Sheaf/FieldTheory/BrauerScalarDefectLifts.lean`, is the proved locally constant
lift construction. `lem-sc-brauer-scalar-defect-cocycle`, in
`lean/Sheaf/FieldTheory/BrauerScalarDefectCocycle.lean`, is the remaining scalar
cocycle construction for those lifts. Both inherit the parent chapter and unit,
carry exact Lean signatures and detailed proofs in words, and cite Stacks
03R6/03R7 and 0DVG. No definition nodes or change records were added.

Ran LeanFinder, Loogle and grep through msearch; they found units/matrix APIs and
Hilbert 90 in degree one, but no exact continuous scalar-defect construction.
LeanSearch returned Internal Server Error and is recorded as unavailable.
The blueprint search for scalar defect returned no duplicate. Library searches
found `Algebra.IsCentral.exists_unit_map_eq_conj`, used in the proved lift step.

## Second reading by R2

1. **Statements and diffs.** Compared the item module with the repository version;
the existing theorem signature is byte-for-byte unchanged. The two new theorem
signatures match their DAG nodes, and no target or existing declaration was weakened.
Verdict: pass.

2. **Compilation and axioms.** Compiled all three modules with the prescribed
`lcompile.py --all` command. The proved lift theorem has no `sorry`; the only
remaining `sorry` is the explicitly split-off cocycle theorem. No forbidden
constructs or hollow definitions occur. Verdict: pass subject to the named split.

3. **New statements.** Checked the lift theorem on the finite-basis construction
and the cocycle theorem on the stated locally constant-lift interface, including
positive dimensions and the n=1 case. The cocycle theorem is strictly smaller than
the parent existential and has its source, proof description, and node. Searches
reported no existing duplicate. Verdict: pass.

4. **Pruning and imports.** The lift proof uses the reduced-norm/Skolem--Noether
import privately; the cocycle interface publicly imports only the scalar-defect
definitions. No unused existing import or proof dependency was found, and the
unit route remains represented by the parent node. Verdict: pass.

5. **DAG agreement.** Updated the parent node's proof and dependencies to the two
actual lemmas, and verified both new nodes record their exact declarations and
proof origins. Verdict: pass.

Changed the parent proof to compose the proved locally constant lift with the
split-off cocycle interface; added the lift and cocycle modules and their DAG nodes.
