## What changed

Proved `ExteriorAlgebra.koszul_conormal_comparison_isIso_top_homology_zero` in
`Sheaf.RingTheory.KoszulConormalTopHomologyZero`, with the original signature and
public imports unchanged. Added three proved private helpers: empty-wedge scalar
expansion, the degree-zero determinant pairing formula, and vanishing of positive
exterior powers of a zero module.

The empty sequence forces `I = ⊥`. Normalization identifies the degree-zero
component with evaluation on the empty wedge followed by the quotient map. Scalar
coordinates prove that component bijective. All positive source and target terms
are zero, so the whole comparison is an isomorphism and its homology map is an
isomorphism. Updated the existing node's proof and dependency record to this route.
No definitions or existing statements were changed; no adaptations are needed.

Local compilation through `lcompile.py` passed with no warnings. Searches used
LeanFinder, Loogle, LeanSearch and Mathlib grep; LeanSearch was unavailable.
Mathlib's `exteriorPower.zeroEquiv`, empty determinant pairing, and componentwise
isomorphism criterion supply the direct route. The proof works for arbitrary
commutative rings, including the zero ring: no nontriviality or positive-rank
assumption is used.

## Proved and sorry left

Closed the sole hole:
`ExteriorAlgebra.koszul_conormal_comparison_isIso_top_homology_zero`
(node `lem-sc-koszul-conormal-top-homology-zero`).

No `sorry` remains in the delivered module. No holes were added and none were
split off. All three private helpers are proved.

## No longer needed

None. No imports were removed or added. The comparison and dual-complex
construction remain necessary. The planned exterior-power degree-zero equivalence
and determinant pairing are used directly from their recorded Mathlib matches.
No planned dependency node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The node's prose statement still quantifies over arbitrary rank, although its Lean
statement and title select rank zero. This delivery preserves the Lean signature
and changes only the proof fields of that node. The positive-rank case belongs to
`Sheaf.RingTheory.KoszulConormalTopHomologyPos` and is not addressed here.

The original plan described computing top cohomology via the incoming image. At
rank zero it is simpler to show the entire comparison is an isomorphism; no
explicit homology quotient calculation is needed. The empty conormal basis
hypothesis is mathematically redundant here but is retained unchanged.

## Second reading by D4

1. Interface: PASS. Compared the sole delivered module against the repository.
   The existing theorem signature is byte-for-byte identical, including all hypotheses,
   its rank-zero conclusion and visibility. No definitions or other modules change.
   Restored the original theorem docstring and removed the newly added copyright header.
2. Proof: PASS. Compiled the module locally using lcompile.py without errors or warnings.
   A scratch copy with #print axioms for the main theorem and all three private helpers
   reports exactly propext, Classical.choice and Quot.sound, with no sorryAx. No sorry,
   axiom, unsafe, opaque, implemented_by or extern occurs in the delivered code.
   Quotient surjectivity supplies only a local scalar in a proposition proof; no data
   is defined using an arbitrary witness from an unproved theorem.
3. Split statements: PASS (none). The sole original hole is closed; zero holes are added.
   Read all three proved helpers. The positive-degree hypothesis is essential because
   degree zero is the coefficient ring even when the original module is zero.
   The main argument also covers the zero ring and imposes no nontriviality assumption.
   There is no disguised restatement or new unproved intermediate.
4. Route and pruning: PASS. Rechecked Mathlib with LeanFinder (trivial-module positive
   exterior powers), Loogle (exteriorPower, Subsingleton; identifier not resolved), and
   rg across Mathlib exterior powers and the repository's Koszul modules. Results confirm
   the existing zeroEquiv and determinant-pairing route. zeroEquiv_symm_apply is an
   alternative to the short scalar-expansion proof, not a shorter overall argument.
   No independent existing theorem gives the required normalized comparison isomorphism;
   its parent and quasi-isomorphism theorems depend on this item. The sole public import
   is needed by the signature. All five old proof dependency nodes remain used, so
   No longer needed is complete. Read dag/units/sk-thm-picard-duality.json (the blueprint source is not installed):
   this item is below its realized statement/step nodes; no unit route changes or pruning.
5. DAG: PASS for the rank-zero Lean item. Only proof, proof_deps and proof_origin differ.
   The dependencies are exactly the union of the proof steps' uses, and all old dependency
   nodes remain. Read their declarations or Mathlib matches; the rewritten steps describe
   the actual empty-wedge, quotient-bijection and componentwise-isomorphism argument.
   The pre-existing prose statement's arbitrary-rank mismatch is already reported above;
   no statement or statement dependency was silently repaired in this proof delivery.

Second-reading changes: restored the original theorem docstring and removed the added
header; added this review record. The checked proof, imports and DAG route needed no repair.
