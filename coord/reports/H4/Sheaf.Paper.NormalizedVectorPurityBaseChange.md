## What changed

Proved `WeilConjectures.PurityFiniteSetting.vectorIntegrationCounit_baseChange` from the independent normalized bundle family and a scalar Cartesian trace identity. The proof explicitly pastes projection exchange, pullback tensor/unitor naturality and the adjunction mate-counit equation. It then derives invertibility of exceptional base change by cancellation. The completed categorical calculation is in the new proved module `Sheaf.Paper.NormalizedVectorPurityBaseChangeCalculus`, with one public theorem and proved private helpers. Explicit component-isomorphism and epimorphism instances avoid expensive general preservation searches. The new proved module `Sheaf.Paper.FiniteNormalizedBaseChange` checks its finite-coefficient specialization with arbitrary source schemes before substituting vector-bundle constructions. The proved `NormalizedVectorPurityBaseChangeComponent` module checks that concrete component calculation separately from choosing the independent primed family.

Added `Sheaf.Paper.VectorIntegrationCartesianTrace` for the remaining scalar trace equation in arbitrary Cartesian presentations. This is a strictly smaller geometric step: it has no exceptional pullback, no purity transformation, no normalization hypothesis, and no arbitrary coefficient-complex input.

Repaired the unclaimed `Sheaf.AlgebraicGeometry.VectorIntegrationMate` proof to use affine adjunctions on every complex and frame descent instead of general smooth tensor duality. Its original public statement and all original private helpers are preserved. The node proof plans follow the actual new proofs. No adopted-source module or target statement is changed.

Compatibility checks: the repaired dependency and six direct importers compiled. The seventh,
`Sheaf.Paper.FiniteRingSectionDeformation` (held by R1), exceeded the limit at 64 seconds with
this repair. A separate baseline run against the original dependency also exceeded the limit,
at 66 seconds. Thus that existing timing failure is not introduced by this proof replacement.
Its original source is untouched. All original private helpers and instances, public signatures,
and public imports are preserved. The temporary consumer copies were removed after checking.

## Proved and sorry left

Closed the item's one direct hole: `WeilConjectures.PurityFiniteSetting.vectorIntegrationCounit_baseChange` (`lem-pur-normalized-vector-purity-base-change`). Added one direct hole: `WeilConjectures.PurityFiniteSetting.vectorIntegration_cartesianTrace` (`lem-pur-vector-integration-cartesian-trace`). Thus this is one decomposition, not a net reduction in holes. The item has zero direct holes; the scalar trace module has one, exactly its named public theorem. `WeilConjectures.PurityFiniteSetting.integrationNormalized_baseChange_calculus` and `WeilConjectures.PurityFiniteSetting.finiteIntegrationNormalized_baseChange` have zero holes.

`WeilConjectures.PurityFiniteSetting.vectorIntegrationCounit_baseChange_component` also has zero holes.

`AlgebraicGeometry.Etale.vectorIntegrationMate_isIso` had zero direct holes and still has zero. Its replacement proof and both new private helpers are complete; no hole was moved into a definition.

## No longer needed

The vector integration mate proof no longer needs the general smooth tensor-duality theorem, `thm-asd-smooth-tensor`, or the coefficient-first tensor-counit specialization `lem-amb-vector-integration-tensor-counit`. The private SmoothDuality import is removed. All original private helpers and instances are preserved for `import all` consumers. The unused private `VectorIntegrationTensorCounit` import is removed. The retained helpers still need their affine and open-exchange dependencies.

The base-change proof uses the right-coefficient form of the already proved projection-exchange theorem directly. The independent canonical trace descent and Tate pullback work remain needed below the new scalar trace statement. No module is withdrawn and no unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The declared geometric trace base-change result is only for the canonical tensor-pullback bundle. The assigned compatibility predicate quantifies over arbitrary Cartesian presentations, whose presentation isomorphism need not be linear or preserve zero. The new scalar identity isolates precisely that missing degree-invariance/pasting step before transposition. `VectorNormalizedTraceCartesian` cannot supply it independently: that module already uses the present theorem.

The existing normalized-family dependency passed through the quarantined false projective-line trace tail via general smooth duality. Its invertibility theorem can instead be proved along the unit's specified affine-adjunction/frame route, without new assumptions or holes.

## New nodes

`lem-pur-normalized-vector-purity-base-change-component` records the proved concrete component calculation before choosing the primed normalized family. It adds no holes.

`lem-pur-finite-normalized-base-change` records the proved finite-coefficient specialization in `Sheaf.Paper.FiniteNormalizedBaseChange`, before substituting vector-bundle schemes. It adds no holes.

`lem-pur-normalized-base-change-calculus` records the completed generic projection, normalization and mate calculation in `Sheaf.Paper.NormalizedVectorPurityBaseChangeCalculus`. It is proved without new holes and is separated from the finite-ring specialization for compilation.

`lem-pur-vector-integration-cartesian-trace` records the remaining scalar integration identity before tensoring with an arbitrary input and transposing. Its module is `Sheaf.Paper.VectorIntegrationCartesianTrace`. Edge checks: rank zero reduces to the pullback-unit laws; the empty base and the zero coefficient ring have unique maps. For a non-linear presentation isomorphism, geometric fibre degree is one, so this statement requires no linearity or zero-section condition. The node records source, proof in words, edge cases, searches and exact Lean attachment.

Change record: `coord/changes/H4-vector-integration-mate-affine-proof.md`.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
