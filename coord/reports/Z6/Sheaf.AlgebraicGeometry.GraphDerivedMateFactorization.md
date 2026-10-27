## What changed

Implemented `AlgebraicGeometry.ProEtale.graph_derived_mate_factorization` without changing
its statement or any public definition. Added proved private categorical helpers for the
localization factors, both counit transposes, and the compactified graph chain. The final
specialization uses the actual graph map selected by its unique graph specification.

The representative equality uses the existing defining factorization of
`Functor.rightDerivedFunctorPlusBaseChange`, after identifying the ordinary graph mate
with the canonical underived comparison. Both specified transposes use the already-proved
`Adjunction.derivedPlus_counit_app_fac` and the specified fixed-comparison counit theorem.
The graph calculation applies the sheaf square termwise, uses naturality of the comparison
unit and the derived mate, and detects equality by fully faithful precomposition with Qh.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.ProEtale.graph_derived_mate_factorization`
(node `lem-sp-graph-derived-mate-factorization`): 1 of 1 holes closed, 0 remaining.
Added 0 holes and 0 split-off statements. All private helpers are proved. The complete
proof compiled in 26.5 seconds; the final delivery checks also validate the style cleanup.

## No longer needed

Removed these proof imports:

- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`;
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`;
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`;
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`.

The direct proof dependencies `lem-pc-pre-derived-adjoint-functors-general` and
`lem-weil-pbc-exact-functor-derived-functor` are replaced by the existing proved bounded-below
counit normalization, recorded by `lem-trf-bounded-below-derived-adjunction`. The general
`lem-trf-bounded-below-derived-mate-model` is also unnecessary: the specified geometric
mate is already constructed as the derived base-change transformation, whose defining
factorization proves the required representative equality directly.

The generic exactness infrastructure nodes `def-weil-pbc-inverse-image`,
`lem-weil-pbc-site-pullback-abelian-exact`, `def-weil-sheaf-of-modules-category`,
`prop-weil-pbc-proetale-constant-ring-map`, `def-weil-pbc-proetale-operations`, and
`lem-sf-comparison-pullback-exact` are not invoked again in this proof: the concrete
functors already have their required additive and exact instances. Their statements and
all adopted source declarations remain available. The old direct dependency
`def-weil-pbc-direct-image` is also unnecessary as a separate proof input: the fixed
comparison definitions already provide the canonical direct-image functors and their
comparison units. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The DAG's route is longer than necessary for these fixed
maps: the defining factorization of the already-constructed derived base-change map gives
the representative equality directly. Re-proving the general pre-derived adjunction is
unnecessary. All public statements and definitions and the unit route are preserved. The theorem
docstring now describes the implemented proof.

The added proof dependency `lem-trf-bounded-below-derived-adjunction` is a closed generic
categorical tool. It records the existing source-library canonical derived adjunction and
its counit formula; it uses no trace-formula theorem or geometric step of that chapter.

Searches used the launcher LeanFinder, Loogle, and grep services and direct searches in
both library roots. LeanFinder returned generic Mathlib derived-counit factorization
lemmas. Loogle did not index the project-specific normalization theorem. The exact
bounded-below specialization was read in the adopted source library and reused.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
