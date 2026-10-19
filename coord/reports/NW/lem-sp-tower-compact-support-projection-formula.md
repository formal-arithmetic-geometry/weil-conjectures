## Worker report

Item: `lem-sp-tower-compact-support-projection-formula`.
Module: `Sheaf.Paper.TowerCompactSupportProjectionFormula`.
Primary declaration:
`AlgebraicGeometry.ProEtale.SpTowerProjection.tower_compact_support_projection_formula`.

The module states the general-field compact-support projection formula on the
ordinary unbounded derived category of varying-coefficient towers. All theorem
proofs are `sorry`. All definitions have concrete data from the recorded functors,
adjunctions, and canonical comparisons. There are no new nodes, dependency repairs,
or changes to the natural-language statement.

I read the node, all eight statement-dependency nodes and their recorded modules,
and paragraph (3) of the current main-20261015 integral direct-image proof. That
paragraph uses the finite-level projection formula to obtain the tower projection
formula before applying derived inverse limit. The helper declarations here all
belong to the maps and clauses of this item; they introduce no independent notion.

Hypotheses and objects, matched individually:

- Prime ell: `(l : ℕ) [Fact l.Prime]` throughout.
- Finite coefficient extension: `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. `SpTowerShriek.R l E n` is exactly the recorded
  ell-power quotient of `Padic.coefficientExtensionIntegers l E` at exponent `n+1`.
  Its coefficient sheaf `SpTowerShriek.B` is the existing `spCoefficientCommRings`.
- Arbitrary positive-characteristic base field: `(k : Type u) [Field k] (p : ℕ)
  [Fact p.Prime] [CharP k p] (hlp : l ≠ p)`. Primality implies positivity; the
  characteristic of a positive-characteristic field is prime. There is no finite
  field datum, algebraic closure, or perfectness hypothesis.
- Separated finite-type schemes: `X Y : Over (Spec (CommRingCat.of k))`, with
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on each structure map.
- A k-morphism: `f : X ⟶ Y` in that over-category. Its underlying map is `f.left`.
- Its arbitrary specified compactification: `c : Compactification f.left`, using
  `c.i`, `c.g`, `c.Z`, their open/proper instances, and `c.comm`.
- Ordinary tower category and operations: `D`, `tensor`, `pull`, `push`, `openD`,
  `F`, and `projection` are imported from `SpTowerShriek`. `b : Base l E` and
  `o : Operations l E b` expose the dependency's normalized simultaneous section
  models. They are presentation data supplied by `tower_shriek_levels`, not
  hypotheses asserting the desired projection formula.
- The recorded abelian-tower presentations are `AX` and `AY`. `realization` is
  `(b.realization T).mapDerivedCategory`, with the existing `A.hasDerived` instance.
  It identifies the actual coefficient-tower derived category with the dependency's
  module-sheaf section-site model; it does not replace towers by diagrams in D.
- `C : D l E X.left` and `B : D l E Y.left` have `constructibleTor` hypotheses.
  This definition is exactly `spConstructibleTorTowers` after the inverse of the
  derived realization. Thus it includes every level's finite constructibility and
  finite Tor amplitude, a single cohomological interval, and a single Tor interval
  independent of the level. It never uses `IsSpNormalizedTower` or an origin witness.

Conclusions and maps, matched individually:

- The first `∃ m : ℤ, ...IsGE m` is bounded-below membership for
  `C ⊗^L f^{-1}B`. The second is bounded-below membership for
  `j_!C ⊗^L p^{-1}B`. These are bounds on the actual tower category.
- `properMap` is pi_p: `adjunction.homEquiv` applied to
  `tensorPullback.hom` followed by `counit tensor identity`.
- The dependency's `o.openTensor` is in the opposite direction to pi_j.
  `Operations.openTensor_mate` specifies its inverse as the open-unit transpose.
  `openMap` applies `push.map` to exactly that inverse. Its domain uses the literal
  iterated inverse image `j^{-1}p^{-1}`, as the displayed pi_j does.
- The primary theorem asserts `IsIso (properMap ...)` and `IsIso (openMap ...)`.
  The extra `IsIso (projection ...)` records their canonical composite after
  `o.comp c.i c.g` and `c.comm` identify the iterated pullback with `f^{-1}`.
- `maps_natural` states both naturality squares for arbitrary morphisms in both
  ambient input categories. The functors `source`, `middle`, and `openSource`
  give the three vertices of the displayed two-arrow diagram.
- `levelTensor` is the existing calculus's finite-level tensor.
  `levelPullTensor` uses the specified tensor-evaluation and inverse-image
  comparisons and `Geometry.tensorPullback`, normalized on pure tensors and total
  K-flat representatives by `Geometry.tensorPullback_eq`. It changes coordinates
  of that canonical finite comparison, without choosing an arbitrary isomorphism.
- `finiteProperMap` is the finite counit transpose, independently constructed by
  the finite constant-ring derived adjunction. `properMap_evaluation` displays the
  equality between evaluation of pi_p and this map, with every tensor, push, and
  pull comparison included. This applies to every positive level and all inputs.
- `levelOpenAdjunction` localizes `finiteOpenAdjunction`, then uses the canonical
  right-derived/exact-functor comparison on its exact right adjoint. This avoids
  imposing a monoidal resolution interface just to derive an exact adjunction.
  `finiteOpenMap` is its finite unit transpose. `openMap_evaluation` states the
  corresponding evaluation equality for pi_j before applying Rp_*. Naturality of
  the recorded `pushEvaluation` identifies the evaluation of `openMap` with Rp_*
  of this same finite map; the source/target comparison is `Fcomparison`.
- `canonicalIso` is `asIso` of the recorded canonical `projection`, using the
  primary theorem's `IsIso` proof. Its forward arrow is the mate composite by
  definition. `canonicalIso_natural` states its naturality on both full Dctf
  subcategories for all ambient morphisms. It does not choose levelwise inverses
  and attempt to lift them.

Dependency declarations used:

- `sk-def-sfb-dc-setting`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `CondensedRing.compactificationOverField` and the explicit standing binders. The
  item supplies an arbitrary compactification rather than selecting that choice.
- `def-weil-l-adic-coefficient-extension`:
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing` and its imported integer-ring constructions.
- `sk-def-sp-coefficient-towers`:
  `Sheaf.Paper.SmoothPurityCoefficientTowers`, `spCoefficientTowers`, `spEllIdeal`.
- `det-sp-coefficient-towers-abelian`:
  `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`, `SpCoefficientTowersAbelian`,
  `spCoefficientCommRings`, `sp_coefficient_towers_abelian`.
- `sk-def-sp-normalized-towers`:
  `Sheaf.Paper.SmoothPurityNormalizedTowers`, `spDerivedCoefficientTowers`,
  `spConstructibleTorTowers`. The normalized predicate is deliberately not used.
- `lem-coef-semilinear-derived-sections`:
  `Sheaf.Paper.SemilinearDerivedSections`, `SemilinearSections.Data`,
  `Geometry`, and their tensor, adjunction and projection-evaluation normalizations,
  through the recorded `SpTowerShriek` interface.
- `def-weil-compactifications-refinements`:
  `WeilConjectures.Compactification.Refinement`, its imported `Compactification`.
- `det-sp-tower-shriek-levels`:
  `Sheaf.Paper.SmoothPurityTowerShriekLevels`, `SpTowerShriek.Base`, `Operations`,
  `D`, `tensor`, `pull`, `push`, `adjunction`, `openD`, `openEvaluation`,
  `finiteOpenAdjunction`, `F`, `Fcomparison`, and `projection`.

All recorded proof-dependency modules that currently have statements are imported
non-publicly unless already reexported by a public statement dependency. The
finite proper-base-change and module-object/ordinary-coefficient-equivalence proof
nodes currently have no recorded Lean declaration, so no module is invented for
them. They occur explicitly in the primary theorem's natural-language proof plan.
The independent naturality and evaluation theorems each have their own proof plan,
and all are listed in `lean.declarations` under this same DAG statement.

Edge cases checked:

- `n = 0` means the first positive exponent 1; no coefficient level is discarded.
- Empty schemes and zero input objects are permitted, with their usual zero
  bounds and identity/zero-object projection isomorphisms.
- Identity maps, open-only and proper-only compactifications remain permitted;
  the constructions reduce to their ordinary adjunction mates.
- Non-normalized towers are included: there is no condition on reduction maps
  being isomorphisms, no surjectivity, and no compatibility of origin witnesses.
- The two uniform intervals are independent, as in the recorded Dctf definition.
- The proper/open direction is checked: the displayed second arrow goes from
  F of the tensor to Rp_* of the tensor; the final forward projection inverts it.
- No independent smaller site universe is imposed. The actual small pro-etale site
  has object universe `u+1` and morphism universe `u`; coefficients are lifted to
  `u+1`, and the ordinary derived model uses its standard localization universe.

Searches for existing declarations:

- `msearch.py ... leanfinder "The compact support projection formula for derived
  varying coefficient towers of sheaves"`: eight unrelated hits, including
  `SheafOfModules.Presentation.map_π_eq` and finite-scalar sheaf comparisons;
  no varying-coefficient tower projection formula.
- `msearch.py ... loogle 'SheafOfModules, "projection"'`: successful, zero hits.
- `msearch.py ... leansearch "The derived projection formula for compactly
  supported direct image of varying coefficient towers of sheaves"`: eight
  unrelated hits (sheaf restriction/projection identities); no matching statement.
- `msearch.py ... grep 'projectionFormula|projection_formula|coefficientTower'
  CategoryTheory`: successful, zero hits.
- `rg` on upstream `WeilConjectures/` and side `lean/Sheaf/` for
  `projectionFormula|projection_formula|lem-sp-tower-compact-support-projection-formula`:
  upstream trace-formula structures and etale finite projection, side finite,
  integral, perfect, scheme-module and tower-operations interfaces. None state the
  present general-field theorem with intrinsic uniform Dctf tower hypotheses.
  In particular `SpTowerShriek.Laws.projection_iso` assumes the finite-field
  geometric setting and finite-level origin witnesses, so is not a match.
- Exact namespace/declaration search in Mathlib, upstream and side sources for
  `SpTowerProjection|tower_compact_support_projection_formula`: no existing hit.

No statement dispute or node fault was found. The source is the current blueprint,
not the superseded master snapshot. Compilation and delivery preflight results
are recorded after running the prescribed wrappers.

Validation: the final module passed `scompile.py NW
lem-sp-tower-compact-support-projection-formula <module>` cleanly, both as the
sandbox module and at its library path (24.8 s and 9.2 s respectively). The
prescribed `deliver2.py ... --no-push` returned
`OK (dry run): commit e6fb77c1a4 passes the preflight and compiles; nothing pushed`.
The wrapper stages exactly the report, the item's node record, and the one module.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
