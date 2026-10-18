## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Etale.closedSupport_torAmplitude` by the five-step proof in
`lem-sf-closed-support-tor-bound`. The theorem's signature is unchanged. The public-import pruning is recorded in
`coord/changes/F2-closedSupport-torAmplitude-imports.md`.

The exact-functor composition, natural-isomorphism, identity and right-derived comparison
APIs lift the given sheaf counit to `D(i^*) Ri_* E ≅ E`. For an arbitrary sheaf `N` on `Z`,
put `M = i_* N`, tensor the supplied distinguished triangle with `M[0]`, and use
`DerivedCategory.HomologySequence.exact₁` at `(r-1,r)`. The two outer objects vanish by
`hQ` and `hK`; `omega` checks the endpoint inequalities using `he`. Exact inverse image
preserves the resulting vanishing by `mapDerivedCategoryHomologyFunctorIso`. The monoidal
pullback comparison and the two counit isomorphisms identify its argument with `E ⊗ᴸ N[0]`.

Added proof-only imports of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`
and `WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat`. The latter supplies
the ordinary module-coefficient flatness-preservation instance required by the existing
monoidal comparison, with no new hypothesis. Both imports pass `import_direction.py may`.
The other proof imports each provide an API used in the proof.
LeanFinder returned t-structure and general homological-functor declarations; Loogle
confirmed `DerivedCategory.HomologySequence.exact₃`, and the source grep returned no
matching Tor-triangle shortcut. The actual first-vertex exact segment is `exact₁`.

The source read was the closed-immersion paragraph of
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/sk-prop-sf-rf-shriek-preservation.proof.md`.
All six declared proof dependencies are used, so the node's existing five-step proof and
`proof_deps` remain accurate. No node, definition or statement is changed. No consumer
imports this item in the shared source at the time of delivery.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.closedSupport_torAmplitude`
(node `lem-sf-closed-support-tor-bound`). Added 0 holes; split off 0 statements.
There are no `sorry`s left in the delivered Lean file. This is a proof from the existing
declared dependencies, including their already recorded proof obligations.

The proof handles `e = 0`, `a = b`, the empty schemes and the zero ring without cases.
For `r < a`, the needed inequalities are `r-1 < a` and `r < a`; for `b+e+1 < r`,
they are `b+e < r-1` and `b < r`. The argument never asserts vanishing at either endpoint.
The distinguished triangle and counit hypotheses are retained exactly as stated.

## No longer needed

Removed these public imports:

- `Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle`: constructing the support triangle
  (`lem-exc-closed-support-triangle`) is not needed, because `hδ` already supplies it.
  The closed-ambient adjoint module stays directly imported for its instance.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`: its additional lower-bounded predicate
  `hasTorAmplitudeGE` is unused. The bounded predicate of `def-kun-tor-amplitude` is used
  directly from the retained `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: none of its additional vocabulary
  is used; the theorem uses `DerivedCategoryModule` from the retained coefficient module.

No declared proof dependency is pruned, no new module is introduced, and no module is
withdrawn. These are removals from this module's imports, not a claim that the corresponding
nodes are unused by the rest of the project. The unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The existing node plan is sufficient without any split.
The earlier imports omitted `FlatModuleCat`, which is needed to specialize the existing
monoidal pullback comparison to ordinary module sheaves. Complementarity `hij` and `hab`
are unnecessary after the distinguished triangle is assumed; the proof retains local copies of
them while preserving the original signature and all hypotheses.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
