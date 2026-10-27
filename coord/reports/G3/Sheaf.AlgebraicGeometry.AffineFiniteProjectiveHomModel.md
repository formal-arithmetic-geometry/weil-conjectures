## What changed

Filled `CategoryTheory.affineFiniteProjectiveHomModel` using the existing finite-free replacement and private helpers for invariance and affine Hom coordinates. Public statement and public imports are unchanged. All additional imports support proofs only.

The finite-free replacement and good truncation give E and G. K-projectivity proves invariance under the two replacement maps. The sheaf Hom terms have finite support and are quasi-coherent. The affine tilde/global-sections counit and explicit linear Hom coordinates give the required complex comparison, including its differential.

## Proved and sorry left

Closed: `CategoryTheory.affineFiniteProjectiveHomModel` (one original hole). Added holes: none. Remaining holes in delivered files: none. This is a proof, not a decomposition into new unfinished statements. The original public signature, docstring and public imports were checked verbatim. Private ringed-site coordinate lemmas and explicit projection calculations keep the differential proof categorical. Exactness of tilde uses the existing `tilde_preservesHomology` theorem, imported privately from `AffineBaseChangeTildeCoordinates`. Its proof uses the global-sections adjunction and injectivity of localization.

## No longer needed

No original imports removed. No existing modules withdrawn or DAG dependencies pruned. The provisional binary direct-sum dependency is unnecessary: the proof uses the existing arbitrary-coproduct closure node instead. The original mathematical route remains needed; the acyclic-cone calculation in its second step is replaced by the existing K-projective fully faithful derived-Hom API and explicit homology-class naturality. The finite-product calculation in its fourth step uses the affine counit and quasi-coherence instead of constructing local matrices.

## Where the brief, the DAG or earlier work was wrong

The plan did not cite the already proved finite-projective-complex free-model theorem. The coproduct dependency now names the existing `isQuasicoherent_sigma` node, rather than the binary direct-sum node. The node records the finite-free replacement, Hom invariance, projection formulas and affine-counit arguments actually used. No statement or definition repair was needed.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
