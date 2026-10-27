## What changed

Proved `CategoryTheory.isIso_of_exact_pair_detects_zero` in
`Sheaf.CategoryTheory.ExactPairDetectsIsomorphisms`, preserving its full signature.
Reused the already proved private `jointly_detect_iso` argument in
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts`: transport vanishing
of the kernels and cokernels of the two image maps along the preservation
comparison isomorphisms, apply joint zero detection, and use the preadditive
mono/epi criteria and the abelian mono-plus-epi theorem.

Removed the proof-only homology-preservation import. Updated the item's proof
plan and dependencies to name the direct kernel/cokernel argument. All public
imports and declarations are preserved; no other module changes.

Searches: LeanFinder for exact functors jointly detecting zero objects, Loogle
for `"IsZero", "kernel"`, and Mathlib grep for the kernel/cokernel vanishing and
mono/epi criteria. Searching the existing Sheaf library found the private helper.
The unit's statement and route are preserved (this node is below its realized
steps). The argument applies without special restrictions to zero objects,
zero categories, or zero morphisms whose two images are invertible.

## Proved and sorry left

Closed 1 of 1 holes:
`CategoryTheory.isIso_of_exact_pair_detects_zero`
(node `lem-cbc-exact-pair-detects-isomorphisms`).
Added 0 holes; split off 0 statements. No sorry remains in the delivered module.

## No longer needed

Removed `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology` from the item's
proof imports. Removed `lem-sp-exact-functor-preserves-homology` from the item's
proof dependencies: only preservation of kernels and cokernels is needed, and
`PreservesKernel.iso` and `PreservesCokernel.iso` are already supplied by the
existing public import `Mathlib.CategoryTheory.Abelian.Basic`.
No project module is withdrawn or claimed globally unnecessary; other users may
still need the homology node.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The plan unnecessarily used
the more general homology-preservation node for its kernel/cokernel clause;
Mathlib's direct comparison isomorphisms implement that clause. The source node
already pointed to the existing private helper, whose proof can be reused here.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
