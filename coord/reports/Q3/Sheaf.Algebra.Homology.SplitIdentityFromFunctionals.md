## What changed

Replaced the first worker's invalid reduction with an explicit construction proving
`ChainComplex.exists_splitting_of_split_functionals`. Its original signature and docstring
are unchanged. The proof constructs the complementary complex on the kernel submodules
and the identity summand on the spans of the specified vectors. Both differentials are
restrictions of the original differential, so their sum commutes with it by linearity.

Added `Sheaf.Algebra.Homology.SplitSubmodulesStable`: explicit kernel and line families,
a proved invariance theorem, and the concrete `restrictToSubmodules` construction.
The target module uses proof-only imports of this module and
`Mathlib.LinearAlgebra.Projection`. Private proved helpers implement the elementary
kernel/span complement, normalized functional equivalence, Boolean-function/product
equivalence, and the direct-sum equivalence. Mathlib supplies
`Submodule.prodEquivOfIsCompl` and `DirectSum.linearEquivFunOnFintype`.

Removed the draft `SplitIdentityCore` and `SplitIdentityCompatibility` modules and their
unlanded nodes. No existing statement or definition was changed, so no change record is
needed. The local unused-variable linter is disabled for the unchanged target signature,
whose existential `g` binder is part of the original API but is used only through its type.

## Proved and sorry left

Closed the one original hole:
`ChainComplex.exists_splitting_of_split_functionals`
(node `lem-weil-pbc-split-identity-from-functionals`).

Also proved the new intermediate theorem `ChainComplex.split_submodules_stable`
(node `lem-weil-pbc-split-submodules-stable`). No holes were added; no `sorry` remains
in either delivered module. This is a complete proof, not a decomposition with open steps.
The draft holes `ChainComplex.exists_splitting_core` and
`ChainComplex.split_core_compatibility` were removed rather than assumed or delivered.
Against the repository baseline: one hole closed, zero holes added.

Both modules compile without errors or warnings through lcompile.py. Explicit
`#print axioms` probes of the target, the stability theorem, and the three public
constructions show only `propext`, `Classical.choice`, and `Quot.sound`, or no axioms.
No `sorryAx`, forbidden declaration, hollow definition, or arbitrary existential witness
is used.

## No longer needed

No repository import, original proof dependency, or reachable module is pruned.
The original dependency `def-weil-pbc-direct-sum-modules` remains used.
The false draft compatibility lemma and unused draft core existence lemma, with their
modules and nodes, are removed from this unlanded delivery; they were not baseline modules.
The new proof depends on the proved stability node and the existing direct-sum definition.

## Where the brief, the DAG or earlier work was wrong

The first worker's `split_core_compatibility` was false: it quantified over arbitrary
complexes and arbitrary degreewise equivalences, with no conditions linking their
maps to the specified kernel/span construction. For a counterexample over ℚ, take C to
be the two-term identity complex in degrees 0 and -1, α=β=id and z=w=1. Take C′ to have
the same graded modules but zero differentials, T to be zero, and ψ the natural identity
from C′⊕0 to C in every degree. All hypotheses about C hold; at degree 0 and x=1,t=0
the claimed compatibility says 1=0. The draft docstring referred to canonical
construction identities absent from its statement.

The draft nodes also copied the parent's statement and old review metadata, had empty
proofs, incorrect Lean file paths, and non-verbatim Lean statements. The parent node's
proof dependencies were not updated to match the draft Lean proof.

The replacement follows the final construction in
[Stacks Project Tag 00MT](https://stacks.math.columbia.edu/tag/00MT), read directly online:
the two separated coordinate summands are preserved by the neighboring maps, and give
the required complex decomposition. Here the kernel and span construction states the
same argument without freeness assumptions, as the original theorem requires.

## New nodes

`lem-weil-pbc-split-submodules-stable`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-split-submodules-stable.json`, records
`ChainComplex.split_submodules_stable` in its own new module. The theorem proves
only invariance of the explicit submodules; it makes no splitting-existence claim and
needs none of the normalizations α(z)=β(w)=1. Its complete proof is in Lean and its
docstring, with source, verbatim signature, elementary proof step, all required search kinds,
creation record, and the parent's chapter/unit/blueprint provenance. No change record.

## Second reading by Q3

1. Signature preservation: PASS. Compared the target file with the repository using diff
and verified the original declaration text through `:= by` byte-for-byte. The target
statement and its existing docstring are unchanged. No existing definitions are modified.
The new definitions construct submodule data explicitly; their proof fields are proved.

2. Proof and trust: PASS after repair. Compiled both files in import order with lcompile.py,
without warnings. Scanned every delivered source for `sorry`, `axiom`, `unsafe`, `opaque`,
`implemented_by`, `extern`, and trust-check bypasses. Explicit axiom probes show only the
three allowed axioms. Removed the false compatibility assumption and both draft holes.

3. New statements: PASS after replacement. No statements are left split off with `sorry`.
The new proved stability theorem is strictly a part of the original construction and does
not restate it. Checked the zero ring, zero terms away from the distinguished degrees,
both neighboring maps, and off-shape differentials. The proof uses no nonzero-generator
assumption and no division. LeanFinder's split-module search found
`lequivProdOfRightSplitExact` and projection tools; the restriction search found
`HomologicalComplex.restriction`, which restricts indices, not module subobjects.
LeanSearch returned Internal Server Error, recorded as unavailable.
Loogle returned no HomologicalComplex/Submodule match. The grep search found invariant
endomorphism tools and index restrictions, but no matching kernel/line invariance theorem.
Searched lean/Sheaf and lean/WeilConjectures for the new constructions and related splits;
no duplicate was found. Used Mathlib's complementary-submodule equivalence for the
assembly rather than introducing an open assembly lemma.

4. Top-down route and pruning: PASS. The construction follows the original four-step plan:
restrict kernels, restrict generated lines, identify the direct sum, and check differentials.
All proof-only imports are plain imports. No original proof dependency is omitted.
Read `dag/units/sk-thm-p1.json`; the target node does not replace a realized unit step,
and the unit's `realized` record and route remain unchanged. No baseline module is pruned.

5. DAG agreement: PASS after repair. Rewrote only the parent's permitted proof and
proof_deps fields to match the actual constructions and the new stability lemma.
The new node has the correct module, path, verbatim statement, source, proof,
proof_origin, all required search records, provenance, and creation metadata. Removed the
unlanded false/mismatched draft nodes and their inherited review claims.

Second reading changed: replaced the invalid decomposition with a complete explicit
proof, proved differential invariance, removed both draft holes/modules/nodes, and
repaired the DAG and report.
