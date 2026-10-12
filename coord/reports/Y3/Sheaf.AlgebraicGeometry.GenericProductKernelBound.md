## What changed

Proved `exists_generic_product_kernel_bound` with its original signature and public imports.
Added two proof-only imports, each containing a completely proved part of the argument:
`Sheaf.AlgebraicGeometry.GenericTensorNilpotenceAnnihilator` and
`Sheaf.AlgebraicGeometry.GenericTensorNilpotenceDescent`.
The first uses tensor localization, finite modules over a Noetherian ring, and Mathlib's
common-annihilator theorem for finite torsion modules. The second clears denominators by
tensor induction and removes unit factors. The main proof constructs the generic tensor
ring equivalence, extends pure-tensor compatibility to all tensors, and reflects nilpotence.
Updated the item's proof route and added the two matching nodes. No definitions, existing
signatures, target statements, or modules held by another group were changed.

## Proved and sorry left

Closed the original hole in `exists_generic_product_kernel_bound`
(node `lem-weil-pbc-generic-product-kernel-bound`): 1 of 1 original sorries proved.
Also proved `exists_generic_tensor_nilpotence_annihilator`
(node `lem-weil-pbc-generic-tensor-nilpotence-annihilator`) and
`generic_tensor_nilpotence_of_annihilator`
(node `lem-weil-pbc-generic-tensor-nilpotence-descent`) from Mathlib alone.
No sorry remains in any delivered module; zero holes added and zero holes split off.
All three modules compile together without warnings. Edge cases include the zero tensor
algebra, an empty generic field product, exponent zero in the nilpotence witness, and the
zero torsion kernel. The proof makes no nonemptiness assumption on the field product.

## No longer needed

No existing imports, dependency nodes, or modules are pruned: the original node had no
proof dependencies and its public imports are retained. Removed unused Finiteness.Defs
and Noetherian.Defs imports from the new descent module and the unused Away.Basic import
from the new annihilator module before delivery. No additional theory of generic splitting,
reduction/localization equivalences, or exactness is needed: the proof works elementwise
with nilpotence and tensor localization.

## Where the brief, the DAG or earlier work was wrong

The original node put the entire calculation into one non-elementary step with no proof
dependencies. It is now realized by two fully proved intermediate statements and an explicit
compatibility calculation. The statement itself needed no correction. The cited blueprint
Markdown file is absent in this checkout; the source reference is preserved, and the argument
follows the complete proof text available in the item's node and declaration docstring,
with proof_origin marked agent. LeanSearch returned Internal Server Error; the recorded
Loogle/LeanFinder and source searches were available. The unit has no realized steps to bypass.

## New nodes

`lem-weil-pbc-generic-tensor-nilpotence-annihilator` records the nonzero uniform scalar
annihilator calculation; its module is GenericTensorNilpotenceAnnihilator and is fully proved.

`lem-weil-pbc-generic-tensor-nilpotence-descent` records denominator clearing and nilpotence
descent after inverting a multiple of that scalar; its module is GenericTensorNilpotenceDescent
and is fully proved. Both nodes inherit sec-smooth-purity and sk-prop-sf-cbc and record the
actual searches. No change record is needed because the existing interface is unchanged.

## Second reading by Y3

1. Interface: compared the existing module and node with the repository by diff.
   The existing theorem signature is byte for byte unchanged. Only its proof and
   two plain proof imports changed; no definitions or target statements changed.
2. Proof: compiled all three modules in import order with lcompile.py, without
   errors or warnings. Independently compiled scratch copies with #print axioms:
   all three theorems use only propext, Classical.choice, and Quot.sound.
   No delivered module contains sorry or a forbidden declaration, and no data is
   chosen from an unproved existence theorem. Verdict: complete proof.
3. Helpers: both new statements are fully proved, strictly intermediate parts of
   the argument, rather than restatements of injectivity. Checked zero B, r = 0,
   nilpotence exponent zero, zero torsion kernel, t = 0 in the conditional descent
   statement, and s = 0. Units handle the degenerate localization cases; the field
   algebra excludes a zero R. Independent Loogle search `IsLocalization, "nilpotent"`
   returned no results; LeanFinder search for a common multiplier into the nilradical
   returned only constituent or different statements. Source searches in both Lean
   roots and Mathlib found no duplicate; the finite torsion common-annihilator lemma
   already used is the relevant Mathlib shortcut. Verdict: true and needed.
4. Route and pruning: read the proof from injectivity down through compatibility,
   generic nilpotence, denominator clearing, and the finite torsion annihilator.
   The proof already uses the direct Mathlib localization and torsion tools.
   New helper imports used only by proofs are plain imports; their public imports
   supply signature vocabulary. Existing public imports remain unchanged.
   The original proof_deps is empty, so there are no omitted old dependencies in
   No longer needed. sk-prop-sf-cbc has empty realized statement and steps lists;
   no realized unit route is bypassed. Verdict: pass.
5. DAG: checked all three nodes against the actual declarations, proof steps,
   proof_deps unions, source references, proof_origin, chapter/unit, creation
   records, and searches. Verdict: pass after the metadata repair below.

Changed only the two new nodes' lean.statement fields to preserve the actual
multiline Lean signatures verbatim, rather than their whitespace-flattened copies.
Added this independent review record. No Lean proof repair was needed.
