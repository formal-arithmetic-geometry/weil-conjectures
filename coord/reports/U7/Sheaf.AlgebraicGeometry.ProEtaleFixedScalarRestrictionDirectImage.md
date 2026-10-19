## What changed

Completed `AlgebraicGeometry.ProEtale.fixedScalarRestrictionDirectImage_kInjective`
in `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage` without
changing any existing public signature or definition. The proof identifies the
underived mate with the identity, transports the derived mate across the canonical
pullback isomorphism, and uses derived-unit naturality and cancellation. It reuses
the proved generic `derived_mate_factors` through a proof-only `import all
Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`. All new helpers are
private and proved. Updated step 4 and proof dependencies of the existing node.
The resumed full-module check compiled successfully in 52.8 seconds through
lcompile.py. The required delivery dry run passed at commit `d69c0e03e8`: the module
compiles and passes preflight, with independent CODEX review required.

## Proved and sorry left

Closed one of the two original holes:
`AlgebraicGeometry.ProEtale.fixedScalarRestrictionDirectImage_kInjective`.

One original hole remains:
`AlgebraicGeometry.ProEtale.fixedScalarRestrictionDirectImageMap_isIso`, node
`lem-weil-proetale-direct-image-restriction-of-scalars`. It still needs the
unbounded global invertibility argument, translating the ringed-sheaf composition
comparison to this fixed-scalar mate. The completed normalization uses this named
invertibility theorem; it does not establish global invertibility independently.

Added zero holes and zero split-off statements. This closes one local hole
conditional on the existing named theorem, not an axiom-free proof of the whole
module. No definition contains a sorry.

## No longer needed

Removed these seven direct proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`

The completed normalization uses the generic mate factorization and unit
naturality, without directly applying the planned ringed-topos composition or
exact-functor-derived comparison declarations. Those nodes remain in steps 1-3
because the global invertibility theorem is still open. Some removed imports are
also transitive dependencies of the retained imports. No module is claimed pruned
from the targets' import closure, and no unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox candidate and report had not passed the full module check;
its specialized adjunction unfolding exceeded the single-file compile limit.
Replaced that calculation with transport through the canonical adjunction
isomorphism and the existing generic derived-mate theorem. No source statement
was found false. The DAG normalization plan has been updated to match the actual
conditional proof; the remaining global argument is not claimed proved.

The static preflight requests a change record for the local proof-transparency
attribute even though it does not export a change. The record is
`coord/changes/u7-fixed-scalar-proof-transparency.md`; no consumer is affected.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
