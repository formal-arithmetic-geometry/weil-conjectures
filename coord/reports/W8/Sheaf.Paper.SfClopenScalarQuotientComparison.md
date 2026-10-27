## What changed

Replaced the hole in `WeilConjectures.sf_clopen_scalar_quotient_comparison` by an explicit assembly of ordinary, degreewise, and derived comparisons. The finite chain isomorphism is obtained from the same ordinary natural isomorphism used by the derived descent theorem; this makes the required counit equation the descent theorem's equation without a choice mismatch. The existing theorem signature and public import are unchanged.

Added four modules: `SfClopenScalarRawRestrictionComparison` proves raw restriction of the sheafified scalar tensor, separated after profiling the generic construction; `SfClopenScalarModuleComparison` constructs the ordinary comparison from cocontinuous restriction of sheafified tensors and normalized ring-isomorphism transport; `SfClopenScalarChainComparison` restricts completed scalars using the projection square and applies the ordinary comparison degreewise; `SfClopenScalarComparisonDescent` proves preservation of K-flatness and descends the ordinary comparison, extending the counit equation from K-flat resolutions to arbitrary complexes by naturality and cancellation.

Private construction and projection lemmas keep completed-coefficient inverse limits out of the final transport elaboration. The coefficient and scalar functors are made locally irreducible after their equations have been proved; instance arguments are normalized before rewriting dependent scalar transports. These are local proof settings, with no shared definition or interface changes.

## Proved and sorry left

Closed 1 of 1 original holes: `WeilConjectures.sf_clopen_scalar_quotient_comparison` (`lem-sf-clopen-scalar-quotient-comparison`). Its statement is unchanged. Added holes: 0. Remaining holes in the assigned module and all four new modules: 0. No sorry statement is split off.

The four new public theorems are proved: `WeilConjectures.sf_clopen_scalar_raw_restriction_comparison`, `WeilConjectures.sf_clopen_scalar_module_comparison`, `WeilConjectures.sf_clopen_scalar_chain_comparison`, and `WeilConjectures.sf_clopen_scalar_comparison_descent`. Their private helpers are also proved. Existing stated dependencies are used as authorized; their modules are unchanged.

Validation: the full sandbox compiled cleanly with `lcompile.py --all`. Individual times were 8.3 s for descent, 47.3 s for raw restriction, 43.2 s for the ordinary comparison, 22.5 s for the chain comparison, and 17.3 s for the assigned module. Every file is below 60 s, with no warnings. No debugging options remain.

## No longer needed

No existing public import or declaration is removed. The assigned node no longer directly needs `lem-pur-clopen-ringed-module-gluing` (`Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing`), `lem-pur-finite-product-derived-tensor-calculus` (`Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus`), or `lem-weil-pbc-site-derived-tensor-descent` (`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`). The ordinary construction uses the more focused cocontinuous tensor comparison and ring-isomorphism transport; derived comparison uses the focused K-flat descent API. These are removals from the assigned node’s direct proof route, not withdrawals. In particular, the ringed module gluing module remains a transitive public import of the generic clopen comparison interfaces, so it is not claimed as a module pruned from the target closure. The other modules may also be used elsewhere and are not withdrawn. `lem-weil-integral-reduction-tower-well-defined` remains needed transitively for the K-flat counit computation. No unit realization is bypassed: `sk-rem-sf-pf-done` has no realized statement or steps.

## Where the brief, the DAG or earlier work was wrong

The original DAG bundles ordinary sheafified tensors, scalar restriction, chain assembly and derived localization in broad proof steps. The implementation records these parts separately and proves their assembly. An arbitrary separately chosen finite chain comparison does not justify the derived counit square: the finite comparison must be induced by the particular ordinary comparison passed to descent. The proof makes that choice explicit. No original statement is disputed or weakened.

## New nodes

`lem-sf-clopen-scalar-module-comparison`: ordinary module comparison with its tensor normalization, without derived or complex assertions. The construction includes empty components, zero coefficient rings, and all indices `n`, with exponent `n + 1` (including `n = 0`).

`lem-sf-clopen-scalar-chain-comparison`: only the completed-coefficient termwise quotient and its section formula. Its scalar-restriction square is constructed using identity maps on underlying sections and `d.projection`.

`lem-sf-clopen-scalar-comparison-descent`: descent from an assumed ordinary natural isomorphism, with the counit equation on arbitrary complexes. K-flatness is obtained by restricting to the two-piece clopen partition and transporting through the completion-ring isomorphism.

`lem-sf-clopen-scalar-raw-restriction-comparison`: the raw restricted-coefficient comparison and its tensor formula. This strictly precedes transport through the prescribed coefficient isomorphisms. It is proved, and was separated after profiling to keep each module within the compile limit.

## Second reading by W8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
