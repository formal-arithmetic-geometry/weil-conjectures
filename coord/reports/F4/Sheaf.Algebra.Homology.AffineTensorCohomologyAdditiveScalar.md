## What changed

The existing theorem `RingTensorCohomology.affineTensorCohomology_additive_scalar`
keeps its exact signature. Its proof combines the additivity and scalar compatibility
components in two new modules, imported only for the proof.
The second reader removed the unused proof imports of `BaseDerivedExtensionLinear`
and `BaseTensorOrdinaryIso`, added missing DAG records, updated the parent node's
proof route, and expanded both split theorem docstrings into complete mathematical
transport arguments. No existing declaration or definition was changed.

## Proved and sorry left

Closed original hole: `RingTensorCohomology.affineTensorCohomology_additive_scalar`
(node `lem-pc-affine-tensor-cohomology-additive-scalar`). Its assembly proof is complete.
Added holes:
- `RingTensorCohomology.affineTensorCohomology_additive_parts`, node
  `lem-pc-affine-tensor-cohomology-additive-parts`.
- `RingTensorCohomology.affineTensorCohomology_scalar_parts`, node
  `lem-pc-affine-tensor-cohomology-scalar-parts`.

This is a decomposition of one hole into two, with net closed minus added = -1,
and not an unconditional proof of the original theorem. No split hole was closed
by the second reading. All three declarations have only `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx` in the scratch `#print axioms` checks.

## No longer needed

Removed direct proof imports:
- `Sheaf.Algebra.Homology.BaseDerivedExtensionLinear`.
- `Sheaf.Algebra.Homology.BaseTensorOrdinaryIso`.

The old dependencies `lem-pc-base-derived-extension-linear` and
`lem-pc-base-tensor-ordinary-iso` remain mathematical dependencies of both split
transport arguments; `def-pc-ring-tensor-cohomology` remains their statement dependency.
Every old proof dependency is therefore accounted for, and no old node is discarded
from the mathematical route. No old module is claimed globally pruned: the underlying
library definitions may still reach these modules. The parent node now lists the
two component nodes as its direct proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The first worker's report claimed two matching new nodes, but no node files were
present in the sandbox. The two split docstrings initially supplied only brief
transport summaries, not complete proofs. The parent DAG still described a direct
transport proof although the delivered Lean only assembled component statements.
The report also omitted the decomposition's hole accounting. These defects are
repaired. The split is limited to the two strict components: neither new theorem
restates the full original conjunction. The substantive natural-comparison work
remains open in the components and is not represented as a completed Lean proof.

## Second reading by F4

1. Signature and visibility: compared the target module against the repository with
   `diff -u`. The existing theorem signature is byte for byte unchanged. Only imports
   and the proof body differ; no existing definition is touched. Verdict: pass.
2. Proof and trust: all three modules compile with `lcompile.py --all`. The main
   assembly is valid conjunction elimination and introduction. The only textual
   `sorry`s are the whole proofs of the two listed public theorems. Scratch
   `#print axioms` checks for all three show only the three allowed axioms and
   `sorryAx`. No forbidden declarations or hollow data definitions occur. Verdict:
   valid conditional proof, with the remaining holes explicitly recorded.
3. Split statements: each is a strict component of the original conclusion, retaining
   exactly the same rings, algebra structures, and degree. Additivity asserts both
   functors preserve sums; scalar compatibility asserts both displayed endomorphism
   formulas. Neither imports the parent, so there is no circular proof. For a zero
   target ring the output modules are zero; for the identity base maps the resolution
   augmentation gives ordinary homology; scalar 0 and 1 give the expected zero and
   identity maps. The derived tensor interpretation handles arbitrary unbounded
   complexes and nonflat ring maps. Read `BaseDerivedExtensionLinear`,
   `BaseTensorOrdinaryIso`, and `RingTensorCohomology`; searched project source and
   Mathlib using `msearch.py` (LeanFinder, Loogle, grep; LeanSearch unavailable).
   `Functor.additive_of_iso` and `ShortComplex.homologyMap_smul` are transport tools,
   not an existing statement of the model identifications. No shorter complete
   proof was found. Verdict: true, strictly smaller components, still open.
4. Route and pruning: the complete original conclusion is reconstructed, and the
   original derived extension / ordinary tensor route remains in the split nodes'
   proofs. Read `dag/units/sk-thm-picard-semicon.json`; its `realized` statement and
   step arrays are empty, and this delivery changes no unit record or chapter route.
   Removed only the two direct proof imports unused by the assembly. Verdict: pass.
5. Metadata: added both missing new nodes with signatures, sources, proof text,
   dependencies, recorded actual searches, origin, creation, and blueprint fields.
   Updated the parent's `proof`, `proof_deps`, and `proof_origin` to match the
   conjunction assembly. New theorem docstrings cite their own node IDs. Verdict:
   consistent with Lean, subject to the recorded two unfinished transport proofs.

Changed in this reading: missing DAG records; parent proof metadata; complete split
proof docstrings; two unused proof imports; accurate hole counts and search evidence.

## New nodes

`lem-pc-affine-tensor-cohomology-additive-parts` states only additivity of source and
target, in `Sheaf.Algebra.Homology.AffineTensorCohomologyAdditiveScalarParts`.
Its proof transports additivity through the natural K-flat comparisons. Stacks Tag
06Y6 supplies derived tensor computation and additivity; Tag 0DJ8 gives the affine
application. Actual search receipts are in `searches.jsonl`.

`lem-pc-affine-tensor-cohomology-scalar-parts` states only the original-base scalar
identities, in `Sheaf.Algebra.Homology.AffineTensorCohomologyScalarParts`. Its proof
transports the derived scalar formula through natural B-linear comparisons and
uses balancing in A tensor_R B. Sources and search evidence are as above.
No statement-change record is needed because no existing signature changed.
