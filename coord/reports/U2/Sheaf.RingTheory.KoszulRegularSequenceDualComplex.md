## What changed

Added `Sheaf.RingTheory.KoszulConormalComparisonExistence`, containing the existence
and quasi-isomorphism part of the normalized comparison, as a proof-only import.
`ExteriorAlgebra.exists_unique_koszul_conormal_comparison` now combines it with a
real uniqueness proof using conormal-vector surjectivity and exterior-pairing
injectivity. All existing declaration signatures and definitions are unchanged.
The augmentation, cohomology, and change-of-generators proofs are retained verbatim.
Updated the original node's proof, proof dependencies and proof origin to record
this reduction. The new module needs only the comparison and regularity imports.

## Proved and sorry left

Hole closed: `ExteriorAlgebra.exists_unique_koszul_conormal_comparison` (node
`lem-sc-koszul-regular-sequence-dual-complex`). Hole added:
`ExteriorAlgebra.exists_koszul_conormal_comparison` (new node
`lem-sc-koszul-conormal-comparison-existence`). This is a decomposition, with
one hole closed and one added, net zero; it does not complete the comparison proof.

Retained proved bodies: `ExteriorAlgebra.koszul_conormal_comparison_cohomology`,
`ExteriorAlgebra.exists_koszul_quotient_augmentation`, and
`ExteriorAlgebra.koszul_conormal_comparison_change_generators`.
Remaining original holes: `ExteriorAlgebra.exists_intrinsic_koszul_ext_determinant`
and `ExteriorAlgebra.koszul_conormal_comparison_localization`, both attached to
`lem-sc-koszul-regular-sequence-dual-complex`. Thus four of the six item theorem
bodies are filled, but their import closure still uses existing open theorems.

## No longer needed

No original proof-dependency node or module is pruned: all five old proof_deps
remain used by the retained proofs or the remaining original proof plans.
No import is removed from the item. Removed redundant direct public imports
`Sheaf.RingTheory.KoszulDualComplex` and `Mathlib.Algebra.Homology.QuasiIso`
from the new module; they are already available through its retained imports.
Exploratory `KoszulDualExactOffTop` and `KoszulConormalTopCokernel` files from the
first worker are absent and are not delivered.

## Where the brief, the DAG or earlier work was wrong

The first report called the newly filled theorem proved without emphasizing the
one-for-one decomposition. Its main DAG node did not yet record the new existence
dependency. Both are corrected. The new node's previous search records did not
match the actual logged queries; replaced them with repeated, logged searches.
Loogle returns `exteriorPower.bijective_pairingDual` from a newer Mathlib, but it
is absent in the pinned Mathlib, so it cannot shorten this proof here.
The cited local calculation agrees with Stacks Tag 0BQZ:
https://stacks.math.columbia.edu/tag/0BQZ . No existing statement is changed.

## New nodes

`lem-sc-koszul-conormal-comparison-existence` is the existence/quasi-isomorphism
part of the canonical comparison, without uniqueness, intrinsic Ext identification,
or localization. Its docstring constructs the top map using evaluation on the
standard top wedge and the dual conormal basis, proves the chain condition modulo I,
and describes the complementary-wedge exactness and top cokernel computations.
It records the conormal-basis and exterior-pairing dependencies, an exact Lean
signature, source, provenance, and four logged searches. No change record is needed.

## Second reading by U2

1. Compared the complete item module with the repository version using `diff`.
   Only one proof body and one plain import changed; every existing signature,
   definition, visibility and docstring is byte-for-byte preserved. No forced
   adaptations or target changes. Verdict: pass.
2. Compiled both files in import order through `lcompile.py`. Checked every delivered
   declaration for forbidden constructs and all seven theorem names with
   `#print axioms` in a scratch copy. Only `propext`, `Classical.choice`, `Quot.sound`
   and `sorryAx` occur. The three remaining holes are exactly those listed above;
   none is in a definition, private theorem, or partial proof. Verdict: pass with
   the explicitly reported open dependencies.
3. Checked the existence statement as a strict part of the argument. Normalization
   determines the comparison, but uniqueness is actually proved in the item,
   rather than assumed. Tested r=0 (I=0, identity quotient), r=1 (dual differential
   is -f, cokernel A/(f)), r=2 (normalizing sign -1), and I=top, including the zero
   ring: no nontriviality hypothesis is needed. Repeated semantic, type-pattern,
   and source searches with msearch.py, and searched the project and upstream
   source. No existing theorem supplies this quasi-isomorphism. The node and
   detailed docstring permit independent takeover. Verdict: valid decomposition;
   the remaining existence calculation cannot be closed in a short repair.
4. Read the reduction from the top. The existing conormal-basis declaration and
   Mathlib exterior-basis formulas supply uniqueness; no further split is needed.
   Retained the correct pairing helper because the newer bijectivity theorem is
   unavailable locally. Removed the new module's redundant imports and confirmed
   compilation. Every old proof dependency remains needed, so no nodes are pruned.
   The unit sk-thm-picard-duality realized record is unchanged; this lower-level
   reduction does not bypass any unit statement or step. Verdict: pass.
5. Matched the original and new nodes against the Lean. Added the missing reduction
   step and its existence dependency to the original node; checked proof_deps is
   the union of step uses. The new node records the actual pairing and conormal
   basis ingredients, matching signature, source, searches, chapter, unit, and
   creation provenance. LeanSearch returned Internal Server Error; its unavailability
   is recorded without claiming a negative mathematical result. The successful
   LeanFinder, Loogle and source-grep searches supply the search evidence.
   Verdict: pass after repair.

Second reading changed: corrected decomposition accounting and search provenance;
updated both DAG proof routes; expanded the new theorem's construction and edge-case
proof docstring; removed two redundant imports from the new module. The correct
Lean reduction itself was retained.
