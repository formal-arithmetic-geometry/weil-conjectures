## What changed

Replaced the sorry in AlgebraicGeometry.Scheme.picard_h1_multiple_locus by a complete
Lean proof from a new cohomological section-lifting intermediate and a proved
proper-shrinking lemma. The existing signature, visibility and docstring are unchanged.
No definition or target statement changed; no other existing module was adapted.

Added Sheaf.AlgebraicGeometry.PicardH1IntersectionSection for steps 1--4 of Tag 0BF2:
a section over the intersection nonvanishing on the marked fibre. Added
Sheaf.AlgebraicGeometry.ProperFibreGeneratorPullbackLocus with a complete Lean proof
of the final proper-shrinking step, universally for arbitrary test schemes. The main
proof derives the intersection point, extends its open neighbourhood to the ambient
base using the immersion's embedding, and combines the factorization properties.
Updated the parent node and added both intermediate nodes to match the Lean proof.

## Proved and sorry left

Original hole closed:
AlgebraicGeometry.Scheme.picard_h1_multiple_locus
(lem-sc-picard-h1-multiple-locus): 1 of 1 original holes replaced by a complete proof.

New theorem proved:
AlgebraicGeometry.Scheme.proper_fibre_generator_pullback_locus
(lem-sc-proper-fibre-generator-pullback-locus), no direct sorry. Its proof removes the
proper closed image of the complement of the nonvanishing open, proves by unique
division that the section is a free generator there, pulls this generator to X_T, and
explicitly composes the module isomorphisms with N = O_T. A separate #print axioms
check confirms this new theorem uses only propext, Classical.choice and Quot.sound.

Only new sorry:
AlgebraicGeometry.Scheme.picard_h1_intersection_section
(lem-sc-picard-h1-intersection-section), exactly `:= by sorry`. Its module/docstring/node
state the intersection construction, perfect direct images, fixed residue models,
joint maximal-minor argument and lift of the fibre generator. It does not assert local
triviality or equality of Picard loci. Its conclusion is the input to the independently
proved proper-shrinking argument, not the original theorem under another name.

This is a decomposition, not a sorry-free proof of the target: one hole closed and one
added, net zero. No sorry inside a definition or partial proof; no arbitrary witness is
chosen to define a public object. Compilation of all three modules passed without
warnings before the metadata was written; the delivery dry run repeats the checks.

Edge cases checked mathematically: n = 0 uses W = S and H1 = 0; source degree-one rank
zero needs no maximal minor. Immersions preserve residue fields at image points, so H1
transfers to w. Nonreduced test schemes remain in the universal quantification. The
proper-shrinking lemma permits empty fibres and empty test schemes without additional
hypotheses. Its proof constructs the open directly from a closed image.

## No longer needed

Removed the direct proof-only imports PerfectDirectImageBaseChange and
PerfectFiniteFreeResidueModel from PicardH1MultipleLocus; these remain necessary in
PicardH1IntersectionSection. They are relocated dependencies, not globally pruned modules.
The old parent proof dependencies are now below the intermediate nodes where needed.
The Picard diagonal universal properties are already hypotheses; its theorem is not
invoked in the final glue. The existing public import PicardDiagonalLocallyClosed is
retained to preserve the existing public environment.

No existing module or node is claimed as globally pruned. In the new proper-shrinking
module, PicardDiagonalLocallyClosed was removed in favour of Mathlib's Proper import;
its theorem and the perfect-complex inputs are unnecessary for that lemma. Also removed
the exploratory proof imports NonvanishingTensorPullback and Modules.InvertiblePullbackTensor:
the final proof uses the existing free-generator pullback and adjunction uniqueness
instead, avoiding their inherited sorries. These were not baseline imports, so they
are not counted as net module pruning.

## Where the brief, the DAG or earlier work was wrong

The previous reverse-direction split retained the complete unproved geometric argument
and was correctly rejected. This delivery proves the proper-shrinking and ambient-open
factorization arguments and isolates only the preceding cohomological section lift.
The original node marked its chain-map construction elementary although it requires
affine derived-category comparison; this obligation is explicit in the remaining
intermediate's proof and docstring.

The sandbox contained 361 stale node copies, including two unrelated changed spectral
sequence nodes. They were removed from this item's delivery; only this item's node and
its two new nodes remain. The theorem-of-cube unit and its route are unchanged.

The Stacks source was read from the existing local literature mirror, at Tag 0BF2 and
its referenced Tag 0BF1 proof. LeanFinder and local searches found no direct replacement;
LeanSearch returned Internal Server Error, recorded as unavailable rather than no match.

## New nodes

lem-sc-picard-h1-intersection-section:
lean/Sheaf/AlgebraicGeometry/PicardH1IntersectionSection.lean;
remaining cohomological lift through d = 0, before proper shrinking. Source Tag 0BF2.

lem-sc-proper-fibre-generator-pullback-locus:
lean/Sheaf/AlgebraicGeometry/ProperFibreGeneratorPullbackLocus.lean;
proved generic proper-shrinking step from a fibrewise nonvanishing section, without H1
or comparison families. Sources Tags 0BF1, 0BF2 and 01CY. No change record is required:
all existing interfaces are unchanged and the new lemmas are imported only by proofs.

## Second reading by H1

1. Compared `PicardH1MultipleLocus.lean` with the repository version. The existing
declaration signature and visibility are unchanged byte for byte; the proof-only imports
were replaced by the two new intermediate modules. No definition or target statement was
changed.

2. Compiled all three delivered modules with `lcompile.py --all`. There are no forbidden
constructs and no `sorry` in definitions. The only remaining `sorry` is the named theorem
`picard_h1_intersection_section`; the proper-shrinking theorem is complete. Axioms checks
give only `propext`, `Classical.choice`, `Quot.sound`, plus `sorryAx` through the explicitly
open cohomological theorem.

3. Read both split-off statements and their docstrings and DAG nodes. The intersection
section statement is a strict cohomological reduction and does not restate the parent;
the proper-shrinking statement is a separately proved universal topological/module lemma.
Both are sourced, edge cases are addressed, and searches found no duplicate declaration.

4. The parent proof follows the shortest available route through the section-lifting and
proper-shrinking intermediates. Removed direct proof-only imports are no longer needed;
the unit route through the intersection and proper shrinking is retained. The new proper
module also avoids exploratory imports that its proof does not use.

5. Checked that the parent and both new DAG nodes agree with the Lean declarations,
including proof dependencies, origins, split status, module paths, and declarations.

Changed during this reading: no Lean statements or proofs; appended this review record
only.
