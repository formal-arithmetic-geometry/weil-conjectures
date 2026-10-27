## What changed

Proved `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalIntegral_rootLevelScalars`
in `Sheaf.Paper.DiagonalIntegralRootLevelScalars`, preserving its statement and public import.
All additional helpers and proof imports are private. The cokernel proof uses the existing
sectionwise criterion in `WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowCokernel`.
Proof-only imports of `ProEtaleTateTwistLevels` and `ProEtaleTateTwistConstructions`
expose their proved linear-map and reduction-epimorphism helpers;
`BaseCoefficientCondensedIdentification` supplies the normalized bottom coefficient
isomorphism, and `ExtendScalarsUnit` supplies the ordinary scalar-unit naturality and
injectivity equations. The proof first shows that the actual
condensed integral reduction is the cokernel of multiplication by the positive prime power.
Pullback and tensoring with the root sheaf preserve this cokernel; the root sheaf kills the
prime power, so the tensor reduction is an isomorphism. Uniqueness of left adjoints identifies
extension of a free module with the free module over the new coefficients. Composing these
isomorphisms gives the finite-level comparisons. The adjunction unit equation and the
coefficient-reduction squares give their prescribed normalization and tower naturality.
Updated the item's node proof, proof dependencies and proof origin to record this argument.
No shared interfaces or other existing modules change. The full single-file proof compiled
in 37.4 seconds; the final packet also applies Lean's local-binding style suggestion.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalIntegral_rootLevelScalars`
(node `lem-diagonal-integral-root-level-scalars`). No holes remain in this module, no new
holes are added, and no statements are split off. Each private helper has a complete proof.

## No longer needed

The proof does not use the planned nodes `lem-diagonal-bottom-finite-root-unit-is-iso`
and `lem-sp-constant-zmod-scalar-tensor` directly. Instead it identifies the actual
quotient-to-root tensor maps by their cokernel universal property and proves the required
scalar comparison with the free/forget and extend/restrict adjunctions. Their modules are
not added as proof imports. This does not withdraw either module or any of its declarations;
other consumers may still need them. No existing public import is removed. No module is
withdrawn and no unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The former plan described the correct quotient-tensor calculation but supplied no ready-made
comparison with the actual reduction map and its scalar-unit normalization. The proof makes
that calculation directly in condensed abelian sheaves and then pulls it back to the scheme,
avoiding any assumption that sections of a sheaf tensor product are algebraic tensor products.
No statement correction is needed. The argument also applies to the empty scheme and to the
bottom coefficient field, and makes no inverse-limit or flatness assertion.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
