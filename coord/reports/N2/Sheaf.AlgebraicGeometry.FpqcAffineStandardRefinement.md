## What changed
Proved `AlgebraicGeometry.Scheme.exists_fpqc_affine_standard_refinement` directly from
Mathlib, with the original signature, docstring, and public imports unchanged. The
finite selection uses `QuasiCompactCover.exists_isAffineOpen_of_isCompact`;
`Scheme.Hom.flat_appTop` and the finite direct-sum equivalence give product flatness;
covering points and pulling primes back along a coordinate evaluation give spectrum
surjectivity. Updated the existing node's proof to match this argument.

## Proved and sorry left
Proved `AlgebraicGeometry.Scheme.exists_fpqc_affine_standard_refinement` (1 of 1 original
open declarations). No sorry remains and no new declarations or split-off nodes remain.
Local compilation and the scratch `#print axioms` check pass with only `propext`,
`Classical.choice`, and `Quot.sound`.

## No longer needed
No original imports, nodes, or proof dependencies are pruned: all four original
proof dependencies are used through their existing Mathlib realizations.
Removed the first worker's proposed nodes
`lem-weil-pbc-fpqc-affine-standard-refinement-data` and
`lem-weil-pbc-flat-product-faithfully-flat` and their corresponding theorems; these
were new sandbox proposals and never landed.

## Where the brief, the DAG or earlier work was wrong
The first worker omitted the covering condition from both intermediate statements.
The proposed faithful-flatness theorem was false: take R = Z and n = 0. Its flatness
and affineness hypotheses are vacuous, but Z to the empty product (the zero ring)
is not faithfully flat. The proposed extraction theorem was vacuous (n = 0 always
works). Both also lacked complete natural-language proofs and valid node metadata.
Mathlib already has the finite affine selection theorem, so neither split is needed.
The original DAG argument itself was correct, including its covering condition.

## Second reading by N2
1. Compared the delivered module with the repository by diff: the sole existing
   declaration's signature is byte for byte unchanged. No definitions, public imports,
   or other visible declarations change. No change record is needed.
2. Compiled the file locally without warnings. There are no sorry, axiom, unsafe,
   opaque, implemented_by, or extern declarations. A scratch copy's `#print axioms`
   shows exactly the three permitted axioms.
3. Rejected and removed both proposed split-off statements after the empty-family
   counterexample above. Repeated leanfinder, loogle, and grep searches with new
   queries; leanfinder located the exact finite affine selection theorem. Read its
   source and the flatness, direct-sum, and faithful-flatness lemmas in Mathlib;
   searched the existing Sheaf algebraic-geometry library as well.
4. The direct proof follows the original finite selection, product flatness, and
   spectrum-surjectivity route. Both original imports are needed by the existing
   signature. No original proof dependency is unused. Read dag/units/sk-thm-iff.json:
   its realized statement and step remain unchanged; no unit step is bypassed.
5. The existing node's proof and proof_origin now describe the actual Mathlib proof;
   proof_deps remains the original four nodes, whose Mathlib realizations are used.
   No new nodes remain to validate.

Changed on second reading: replaced the invalid split by a complete direct proof,
restored the original documentation, removed both proposed nodes, and repaired the
proof metadata and this report. The target statement is unchanged.
