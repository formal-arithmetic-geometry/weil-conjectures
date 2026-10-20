## What changed

Filled all four original theorem holes in Sheaf.Paper.SupportedCup. Restriction of constants is
identified with the conjugated lax direct-image unit. The supported-constant cokernel
presentation makes restriction epic; tensoring preserves these epimorphisms, giving uniqueness
of the normalized multiplication map.

For the ordinary coefficient isomorphism, transport the existing etale closedConstantTensor
isomorphism through strong monoidal comparison and its base-change isomorphisms. Proved private
helpers identify the comparison unit with cupConstantIso and verify the exact normalization,
so the uniqueness theorem identifies the transported arrow with cupCoefficientMap. Flatness
uses etale open-closed flatness and comparison. The derived comparison uses the flat single
complex, K-flat localization comparison, and the ordinary isomorphism. Its private helper
transports the monoidal and localization structures together as a dependent pair.

All public signatures and coefficient data are preserved. The existing localization/monoidal
references use reducible transparency, cupDerivedCoefficientMap is irreducible, and supportedCup
names its existing C, L, M and N arguments explicitly. These repairs keep elaboration within the
compile limit. Explicit categorical associativity rewrites prevent kernel checking from
expanding concrete sheaf-map compositions. The complete change record is coord/changes/SupportedCup-proof.md. Only the
copied node's proof, proof_deps and proof_origin fields are updated. All new helpers are private
and proved; proof imports remain private.

## Proved and sorry left

Closed 4 of 4 original holes:

- AlgebraicGeometry.ProEtale.cupCoefficientMap_existsUnique.
- AlgebraicGeometry.ProEtale.cupCoefficientMap_isIso.
- AlgebraicGeometry.ProEtale.cupCoefficient_flat.
- AlgebraicGeometry.ProEtale.cupDerivedCoefficientMap_isIso.

No sorry remains in the delivered Lean module. No holes were added or split off. The ordinary
isomorphism uses the existing stated AlgebraicGeometry.Etale.closedConstantTensor theorem;
its separate module and existing hole are unchanged.

The complete module compiled with build artifacts in 34.7 seconds, with no warnings. The
epicity proof includes empty supports and zero coefficients. The flatness proof needs no quasi-compactness of an open complement.
PurityFrameClass compiled unchanged against these definition repairs in 52.5 seconds.
SupportedCupFunctoriality and SupportedExteriorClasses exceeded the 60-second limit both
against the published module and against the revised definitions. These baseline failures do
not establish forced adaptations; neither consumer is changed. The maintainer's global build
remains the final check of these consumers.

## No longer needed

None pruned. All original public imports and all source-library declarations are retained.
The separate balanced quotient/ideal-sum isomorphism calculation and inline idempotent
flatness calculation are unnecessary: the existing etale tensor and flatness theorems give a
shorter route after canonical comparison. The supported-constant quotient presentation is
still used for epicity and uniqueness. No node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The blueprint's stalkwise shorthand does not supply conservativity on arbitrary pro-etale
sheaves. The implemented proofs use the etale statements and the actual comparison functor;
they impose no geometric-stalk conservativity assumption on pro-etale sheaves. No statement
was weakened or marked disputed.

During metadata editing, one command mistakenly rewrote the shared node JSON without changing
its fields. The changed delivery node is in the sandbox. No shared Lean source was edited.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
