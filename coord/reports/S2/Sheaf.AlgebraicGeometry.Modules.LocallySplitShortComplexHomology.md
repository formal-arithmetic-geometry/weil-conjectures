## What changed

Proved the original theorem without changing its signature. Three private, fully proved helpers identify homology with the image-to-kernel cokernel, prove the rank of a split cokernel via affine projectivity and stalk-rank additivity, and glue over the given splitting neighbourhoods. Updated the node's proof route. The second reading removed the redundant proof-only import `Mathlib.Algebra.Homology.ShortComplex.ShortExact`, corrected helper documentation, and restored the dependencies actually used.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_homology_of_locally_split_image`, the item's only original hole. No sorry remains and no hole was added. All three private helpers are proved.

## No longer needed

Removed imports `Sheaf.RingTheory.FiniteProjectiveStandardFreeCover`, `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`, and the redundant direct import `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`. The proof no longer needs the DAG dependencies `lem-weil-pbc-finite-projective-standard-free-cover` and `lem-weil-pbc-quasi-coherent-module-cokernel-image` or the full affine tilde/gamma adjunction node `lem-weil-pbc-affine-tilde-gamma-adjunction`. Also removed the redundant `Mathlib.Algebra.Homology.ShortComplex.ShortExact` import during second reading. The old dependencies `def-amb-finite-locally-free-module` and `lem-weil-pbc-projective-direct-summand` remain used (the latter is Mathlib's already proved `Module.Projective.of_split`); finite local freeness is handled by already proved source-library criteria. No assertion is made that these modules are globally unreachable from other targets.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The original plan's standard free cover can be replaced by the source library's affine finite-local-free criterion and additivity of stalk ranks. The proof works on an empty scheme without asserting b ≤ k globally.

## Second reading by S2

1. Compared the sole delivered Lean module against the repository with diff. The existing public theorem signature is byte for byte unchanged; no definition, hypothesis, or conclusion changed. All added declarations are private, fully proved proof helpers. The retained public import is unchanged; every added import is proof-only.
2. Compiled the module with lcompile.py without errors or warnings. In a scratch copy, printed axioms of the public theorem and all three private helpers: each uses only propext, Classical.choice, Quot.sound. No sorry, axiom, unsafe, opaque, implemented_by, extern, or hollow definition occurs. The retractions and isomorphisms come from proved categorical constructions, not unproved existence witnesses.
3. No sorry was split off and no hole was added. Read each helper: the cokernel argument is a genuine retract construction, the homology identification proves the universal property, and the local helper restricts the given retraction. Empty schemes impose no global b <= k; at each affine prime additivity gives k = b + quotient rank. For b = 0 the rank is k, and for k = b it is zero. Independent searches via msearch.py grep and rg in Mathlib, source modules and Sheaf found no shorter theorem with the same conclusion. Mathlib's LeftHomologyData.ofAbelian uses a different coimage presentation; the explicit cokernel universal-property proof here is justified.
4. The proof closes the original hole directly from proved Mathlib and source-library facts. Removed the unused ShortExact import (compilation still passes); Biproducts is required for ModuleCat.biprodIsoProd. The No longer needed section lists every old proof dependency now unused. The unit sk-thm-picard-semicon retains its kernel/image direct-summand quotient step; its realized fields name no nodes, so no realized unit step is bypassed. No unit record changed.
5. Corrected the node: retained the finite-locally-free notion and projective-direct-summand dependency, added the existing affine-sections-projectivity and quasi-coherent-cokernel-closure nodes, and marked the substantial second step non-elementary. Named the already proved rank criterion, stalk-rank calculation and gluing declarations in its proof text. Removed helper references to nonexistent blueprint nodes and aligned the public proof docstring with the actual affine criterion argument. Node statement and Lean signature remain unchanged. No new nodes or change records are needed.

Second reading changes: redundant proof import removed; helper comments, public proof documentation, DAG dependencies and pruning report corrected. No proof term required repair. Closed one original hole and added zero holes.
