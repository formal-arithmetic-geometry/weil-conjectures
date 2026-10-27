## What changed

Proved `AlgebraicGeometry.Etale.FiniteSmoothPurity.normalExchange_integration` in
`Sheaf.Paper.FiniteSectionIntegratedSpecializationIntegrationBaseChange` from the existing
Cartesian vector integration trace theorem, restriction of coefficient squares to sections,
and section exchange transitivity. The cone-to-bundle isomorphisms transport the given
normal exchange to an arbitrary Cartesian presentation of vector bundles. A new proved theorem,
`AlgebraicGeometry.Etale.FiniteRingSectionDeformation.bundleSectionAdjoint_baseChange`,
in `Sheaf.Paper.FiniteBundleSectionAdjointBaseChange` carries the bundle calculation.
Three proved private helpers carry the adjunction, compositor and inverse calculations.
The bundle calculation was extracted after profiling and caching derived-category
instances to keep each module within the compile-time limit.
Both modules compiled in import order (39.7 s and 33.2 s respectively); the final
packet removes the development profiling options. Updated the item node to record
this proof route. No other existing module is changed. The normal zero sections are written with fully
qualified names in the signature to avoid field-notation elaboration failures; the
elaborated statement is unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.FiniteSmoothPurity.normalExchange_integration`.
The item contains zero `sorry`; zero holes are added and no unproved statements are split off.
The new bundle theorem is also proved without `sorry`.
The proof uses existing named dependencies, including the still-unproved
`WeilConjectures.PurityFiniteSetting.vectorIntegration_cartesianTrace`; those existing
obligations remain with their existing nodes.

## No longer needed

Removed the proof import
`WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange`.
The proof does not need smooth exceptional exchange to be invertible; the statement already
supplies invertibility of its two normal section maps.

The planned dependency
`lem-sp-finite-section-integrated-specialization-normal-exchange`
(`Sheaf.Paper.FiniteSectionIntegratedSpecializationNormalExchange`,
`AlgebraicGeometry.Etale.FiniteSmoothPurity.normalExchange_exists`) is not needed by this
proof: the map `ν`, its Cartesian square and its zero-section equation are already arguments.
That node remains needed by the parent construction; no module is withdrawn.
No other planned dependency is pruned. The unit's vector integration route is retained.

## Where the brief, the DAG or earlier work was wrong

The original item node cited only existence of a normal exchange, which does not imply the
integration equation. The proof instead uses the existing scalar trace base-change theorem
and the existing functoriality of the actual counit-defined exchange maps. In particular,
no compatibility of conormal linear presentations has to be assumed: the scalar trace theorem
already permits arbitrary Cartesian presentations. Empty schemes, dimension zero and the
zero coefficient ring need no additional cases or hypotheses.

The vector integration theorem belongs to unit `sk-prop-an`; it is used here as the vector
integration tool explicitly called for by the orientation step of `sk-prop-sp-purity-bc`.
No unit statement or route is changed.

## New nodes

`lem-sp-finite-bundle-section-adjoint-base-change` records the proved restriction of
vector integration adjunct base change to zero sections. Its source is proof (1) of
`sk-prop-sp-purity-bc-factors.proof.md`, the normal-bundle integration step. It is a
strict intermediate calculation: it has no normal cone, cone comparison or inverted
normal section map. It introduces no proof obligation. No change record is required:
no existing signature, definition, public import, instance or attribute changes.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteBundleSectionAdjointBaseChange": "aba00185667fade0fc13ff954d1d56e7159ee70f", "Sheaf.Paper.FiniteSectionIntegratedSpecializationIntegrationBaseChange": "36f331a10ff2709ab1365c2cf944b84251aaf59d"}, "own_failed": ["Sheaf.Paper.FiniteBundleSectionAdjointBaseChange", "Sheaf.Paper.FiniteSectionIntegratedSpecializationIntegrationBaseChange"], "results": {}, "time": "2026-10-28T03:45:47+0800", "transitive": 0, "version": 1}
```

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
