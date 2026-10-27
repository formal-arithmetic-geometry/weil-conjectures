## What changed

Filled the two original finite-level comparison holes by explicit ordinary adjunction constructions. First transpose the two scalar/reduction units through the source reduction adjunction, using compatibility of the completed scalar map with the quotient maps. This gives the normalized finite coefficient map, natural in module sheaves and compatible with differentials.

For pullback, apply the existing finite pullback mate construction to that map, restrict through the coefficient square and transpose through completed ordinary scalar extension. The adjunction unit equations give the required section formula. Module naturality gives the chain-map equations and complex naturality. The existing `scalar_pullback_hom_ext` proves uniqueness.

For tensor, apply the existing signed total tensor chain-map construction to the two finite coefficient maps, restrict coefficients and transpose through scalar extension on complexes. The total-tensor pure-section formula gives the required normalization. The existing total-tensor and restricted-chain-map naturality lemmas, followed by adjunction naturality, give a natural transformation. Scalar adjunction injectivity and `finite_tensor_ext` prove uniqueness.

The four new proof modules separate elaboration costs. They contain fully proved theorems, not new obligations. The existing module's public imports, all declaration signatures, all data definitions, and the unit route are unchanged. No adopted source-library file is changed.

Validation: all four construction modules passed the server single-file compiler in import order. The completed item then passed the server compiler (24.9 seconds reported), including both uniqueness proofs and every pre-existing proof in the file. No profiling options or diagnostic declarations remain.

## Proved and sorry left

Closed 2 of 2 original holes:

- `WeilConjectures.scalarPullbackLevel_existsUnique`.
- `WeilConjectures.scalarTensorLevel_existsUnique`.

Added 0 holes; split off 0 unproved statements. No `sorry` remains in any delivered Lean file. The new theorems `WeilConjectures.integralScalarFiniteReductionMap_existsUnique`, `WeilConjectures.integralScalarPullbackLevel_exists`, `WeilConjectures.integralScalarTensorChain_exists`, and `WeilConjectures.integralScalarTensorLevel_exists` are proved. The pre-existing tower, Roos and good-complex proofs remain in place. These proofs use existing library declarations, whose independent remaining obligations remain governed by their own nodes.

## No longer needed

Removed ten unused private imports from the item:

- `Sheaf.Paper.CompletedIntegralFiniteFree`.
- `Sheaf.Paper.NormalizedIntegralScalarCompletion`.
- `Sheaf.Paper.NormalizedIntegralOrdinaryTensorChain`.
- `Sheaf.Paper.IntegralScalarInternalHomComplete`.
- `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData`.
- `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeTensor`.
- `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeHom`.
- `Sheaf.Paper.TensorPullbackRepresentativeDescent`.
- `Sheaf.Algebra.Homology.ScalarHomComparisonTower`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`.

The finite-level proofs need neither a completed scalar isomorphism nor a finite-free coefficient basis, a derived internal Hom comparison, or representative descent. They directly construct the ordinary normalized maps from the existing adjunction and total-tensor APIs. No existing module or declaration is withdrawn. The actual scalar adjunction is `CategoryTheory.CochainPullback.extensionAdjunction`, owned by `def-pur-cochain-coefficient-arrows`, transferred through the existing tensor presentation. The separate existential theorem `lem-pur-sheaf-ring-coefficient-ordinary-adjunction` and the rational-category composition theorem `lem-weil-scalar-extension-composition` are not applied. The finite pullback mate and its adjunction are already constructed in `IntegralOperationsWellDefined`, so the standalone ringed-topos and continuous-site adjunction nodes need no new direct import. The generic adjunction, local-surjectivity and tensor ingredients remain needed through the existing proof APIs; no transitive source-library declaration is declared obsolete.

## Where the brief, the DAG or earlier work was wrong

No false statement was found and no statement or definition was repaired. The seven-step pullback plan and signed-total-tensor plan are implemented, reusing already proved private adjunction, mate and generator-extensionality helpers rather than rebuilding them. The profiler identified repeated elaboration of adjunction and restriction presentations in the combined proof file. Local irreducibility for the constructed maps and adjunctions, the existing generic tensor chain map, explicit projection-square transport, explicit equality composition and simplification of the named section definitions reduced unfolding without changing the shared definitions. The combined file still exceeded the compile-time limit, so the shared reduction construction and the two existence constructions were then factored into separate proved modules. The tensor chain construction and its naturality/assembly were separated after profiling showed approximately 20 seconds to elaborate the explicit adjunct and 30 seconds to check the naturality conversion in the combined tensor file. This changes no mathematical dependency or public data model. The original two nodes now record existence followed by the actual extensionality argument for uniqueness.

Edge cases checked in the construction: zero modules and complexes, identity morphism and scalar embedding, empty schemes, n=0 (quotient exponent 1), ramified scalar embeddings, and arbitrary unbounded complexes. The coefficient square supplies the balancing relation; no coefficient map is assumed invertible, and no assertion that every sheaf section is globally a pure tensor is used.

## New nodes

- `lem-pur-integral-scalar-finite-reduction-unit-map`: the normalized finite reduction map obtained by transposing the two units; uniqueness is tensor-section extensionality. Its private naturality and chain-map implementation is shared by both consumers. Fully proved.
- `lem-pur-integral-scalar-pullback-level-construction`: existence of the normalized natural pullback comparison, built from the ordinary finite pullback mate and scalar adjunction. Fully proved; uniqueness remains and is proved in the item.
- `lem-pur-integral-scalar-tensor-chain-construction`: a chain map for each pair of finite tensor complexes, normalized on every homogeneous tensor generator, with no naturality assertion. Fully proved.
- `lem-pur-integral-scalar-tensor-level-construction`: existence of the normalized natural signed-total-tensor comparison, built from the existing tensor map and scalar adjunction. Fully proved; uniqueness remains and is proved in the item.

Searched the DAG, latest blueprint and Mathlib for these constructions. The blueprint's derived coefficient-change isomorphisms are broader downstream assertions, not these specified finite ordinary representative maps. Mathlib supplies generic scalar extension, pullback composition and total-tensor ingredients, not the required normalized coefficient-square transformations. The new nodes record the searches and source proofs.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
