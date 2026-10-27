## What changed

Proved `CochainComplex.augmentedResolution_extension_cone_lift` in
`Sheaf.Algebra.Homology.AugmentedResolutionExtensionConeLift` with its original signature.
The kernel universal property gives the unique factorization and its cocycle equation.
Mathlib's `HomComplex.Cocycle.toSingleMk`, `Cochain.toSingleMk`, and `mappingCone.lift`
construct the cone morphism. Its negative triangle projection supplies `fbar`, with the
required sign and component equations. Exactness of the single-degree functor and
`mappingCone.quasiIso_descShortComplex` give the cohomology and derived-category assertions.
Added one private proof import, `Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle`.
Updated the item's node proof to describe these constructions and the exact-functor shortcut.
All existing public imports, definitions, statements, and signatures are unchanged.

## Proved and sorry left

Closed the one original hole:
`CochainComplex.augmentedResolution_extension_cone_lift`
(node `lem-sfb-augmented-resolution-extension-cone-lift`).
Holes added: zero. Holes remaining in the delivery: zero. No split-off statements.
The proof uses proved Mathlib declarations only.
The single-file server compile passed with no errors or warnings, within the 60-second limit.

## No longer needed

No imports, modules, or dependency nodes are removed. All declared proof dependencies remain
used: the abelian complex-category instance, kernel universal property, short exact cone
quasi-isomorphism, exact-sequence definitions, and derived-category constructions.
The degreewise short-exactness calculation is replaced by `ShortExact.map_of_exact` for
the single-degree functor; the node carrying that calculation also supplies the abelian
complex-category instance, so it remains a dependency.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The hypotheses that `P` vanishes in positive degrees
and that `e` is a quasi-isomorphism are stronger than the construction needs; the original
statement is retained verbatim. Mathlib's existing APIs carry out the full planned argument.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
