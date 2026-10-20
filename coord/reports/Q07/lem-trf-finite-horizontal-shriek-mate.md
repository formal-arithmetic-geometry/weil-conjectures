## Worker report

The delivery states `WeilConjectures.finiteHorizontalShriekMate` in
`Sheaf.Paper.FiniteHorizontalShriekMate`; its proof is `sorry`. The canonical arrow χ is
owned by the new definition node `def-trf-finite-horizontal-shriek-composition` in
`Sheaf.Paper.FiniteHorizontalShriekComposition`, with real data and no postponed definition.
It also reexports the intrinsic finite-Tor predicate with a transparent alias.
That module also exposes `finiteHorizontalProperOpenComparison`, a direct interface to the
published `sfProperOpenDerivedComparison` construction. This is equation (C) of the node's
proof: the published proper/open comparison followed by the direct-image square
isomorphism conjugate to the canonical pullback square. Associators only fix the
parentheses of those functor composites. This is not a chosen arbitrary isomorphism.

Hypothesis and clause correspondence:

- `T : TraceFormulaCoefficientConventions.{u}` fixes the entire global finite-field
  datum and the positive quotient level. `T.coefficientRing` is exactly A_{E,n},
  `T.coefficientField` is the specified finite extension, and `T.level_pos` is n≥1.
  The theorem signature supplies `Finite T.coefficientRing` explicitly with
  `letI := Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField
  T.level T.level_pos`; no comparison theorem is imported for a plain instance.
- The four objects are `Scheme.{u}` with `Over (Spec (.of T.datum.k))` instances.
  `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` of each structure morphism
  express exactly separated finite-type k-schemes. The four `IsOver` instances express
  the four specified k-morphisms. No descent to T.X₀ is imposed on these four schemes.
- `sq : ChosenCartesianSquare p f' f g` includes commutativity and the chosen pullback
  identification. `IsPullback.of_iso_pullback` uses that identification to supply the
  actual Cartesian square, not a merely commutative replacement.
- `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` render the separately named
  separated finite-type hypothesis on f; `IsFinite g` is the finite bottom arrow.
  The first conclusion is `IsFinite p`; this is not an assumed instance.
- `c : Compactification f` is arbitrary. Its specified Cartesian base change is
  `c.ofIsPullback ...`; `pullback.fst c.g g` is the finite horizontal arrow on proper
  ambient schemes. The published `isPullback_i_ofIsPullback` and
  `isPullback_g_ofIsPullback` give the open and proper squares in the actual exchange.
- `K : (finiteHorizontalFiniteTorConstructible ... X).FullSubcategory` quantifies over precisely the
  bounded constructible intrinsic pro-etale objects with finite Tor amplitude, using
  the existing predicate and its full-subcategory inclusion `K.obj`.
- `sfIntrinsicCompactSupport c T.coefficientRing` is the recorded open extension
  followed by the proper direct image. `sfExchangeShriek ...` is exactly the existing
  compactification-defined exchange, using proper exchange and the specified open
  exchange. Independence of c is the cited dependency's property of this chosen map;
  no arbitrary exchange transformation is supplied as an assumption.
- Both units are explicitly those of
  `(sfIntrinsicConstantModuleAdjunction ...).mapDerivedCategoryRightDerivedAdjunction`.
  These are ordinary constant-module pullback/direct-image adjunctions. There is no
  completion or exceptional inverse image in either unit.
- Lean composes left to right: the left side is `η_g.app (Rf! K) ≫ Rg*.map (Ex!.app K)`;
  the right side is `Rf!.map (η_p.app K) ≫ χ.app (Lp* K)`. This is exactly the node's
  displayed equality, with all endpoints inferred in the same intrinsic category.
  The final inverse-square-mate sentence is the equivalent adjunction formulation of
  this equation, not an additional hypothesis or an independently stronger clause.
  The proof docstring includes the inverse-mate formula and its Hom-bijection argument.

Dependency declarations used in the signature and real construction:

- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions` and its coefficient abbreviations.
- Mathlib `AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`; scheme
  morphism properties use Mathlib's existing `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact` and `Scheme.Hom.IsOver` classes.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` and its intrinsic realization:
  `proEtaleConstantDerivedDirectImage`, `sfIntrinsicDerivedPullback` and
  `sfIntrinsicConstantModuleAdjunction` (the latter in `SfIntrinsicRealizationTransport`).
- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`.
- `Sheaf.Paper.SfExchanges` (publicly reexported by the recorded
  `Sheaf.AlgebraicGeometry.SfEtaleExchanges`):
  `AlgebraicGeometry.Scheme.sfExchangeShriek`, which specializes
  `SuppliedExchangeProjection.compactificationExchangeFromData` from
  `Sheaf.Paper.ExchangeProjectionSuppliedDomains` to the actual canonical operations.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: `sfIntrinsicCompactSupport`;
  `ProEtaleOpenSquareExchange`: `sfIntrinsicDerivedSquarePullback`.
- `Sheaf.Paper.FiniteHorizontalShriekComposition`: `finiteHorizontalProperOpenComparison`
  is the direct interface to `sfProperOpenDerivedComparison`, whose definition transposes
  inverse sectionwise restriction using the actual open adjunctions; the same module defines
  `finiteHorizontalShriekComposition`.
- Mathlib `CategoryTheory.Adjunction.Mates`: `conjugateIsoEquiv`, with
  `CategoryTheory.Adjunction.comp`; the inverse-square-mate convention is
  `mateEquiv` and `unit_mateEquiv` in that same module.

Every published proof-dependency module is imported, including
`ExchangeFunctoriality`, `ProperCompositionSiteTransport`, `ProperOpenSiteTransport`,
`ProperOpenInterchangeCoherence`, `ProperSupportSheafComposition`, the module/abelian
comparison, `ExactUnboundedExchange`, direct-image composition, proper coincidence,
constructible origin, canonical comparison mates and open site transport. The twelve
proof steps in the theorem docstring reproduce the node's normalized (O), (P), (C)
route and its site transport; no proof is supplied. The old `prop-functor-package`
record names a Weil-complex base-change theorem rather than a composition constructor;
χ is therefore written using the actual normalized proper/open model in Step 6 and
its published constituents, not selected from that theorem's mere Nonempty result.

The new definition node `def-trf-finite-horizontal-shriek-composition` is added to
`stmt_deps`; it owns the χ construction and its proper/open interface. The proof route and its existing `proof_deps` are retained; the two unrelated theorem
nodes are no longer added to `stmt_deps` merely for their plain constructions.
The statement, proof and proof_deps of the item are unchanged.

Edge cases checked: all four schemes may be empty; K may be zero; g may be an identity,
a finite closed immersion, or a finite non-flat/non-etale map. No smoothness or flatness
is assumed. f need not be proper, so the open-extension factor is retained. Arbitrary
positive levels, including n=1, and every scheme universe u are covered. There is no
finite-cohomological-dimension, origin-witness, arbitrary adjunction or arbitrary
comparison-map hypothesis. The separate finite-Tor condition is retained.

Searches (logged also in searches.jsonl):

- `msearch.py ... leanfinder "compact support base change exchange finite horizontal
  maps unit adjunction mate composition proper direct image"`: eight generic adjunction
  and module-pullback hits, no exact finite-horizontal compact-support assertion.
- `msearch.py ... loogle "CategoryTheory.mateEquiv, CategoryTheory.unit_mateEquiv"`:
  `CategoryTheory.unit_mateEquiv`, the generic mate-unit identity, not this node.
- `msearch.py ... grep "mateEquiv|compactSupport.*[Mm]ate" CategoryTheory/Adjunction`:
  five hits in Mathlib Mates.lean; no scheme compact-support specialization.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the item id and finite-horizontal
  compact-support/mate names, plus `grep -rn` for the item id upstream: no declaration
  already states this node. Existing pullback, exchange, finite-Tor and canonical
  proper/open declarations found in these searches are reused as listed above.

Validation: the repaired three-file intermediate packet compiled on the server through
scompile.py (22.9 s, 8.8 s, 22.9 s). The final two-file packet passes deliver2.py
preflight and compilation. The 60-second limit was never raised. The final dry-run and
push commands record compilation of every delivered file.

## New nodes

`def-trf-finite-horizontal-shriek-composition`: the module defines the published proper/open
comparison interface, transparent intrinsic finite-Tor domain alias, and the χ compositor from `Rb_*(γ)` followed by the conjugate pullback
square isomorphism σ, with associators. The source is proof (β), normalized equation (C),
of `lem-trf-weil-shriek-operator-fibres`; searches found no existing DAG or upstream
finite-horizontal compositor, while the constituent comparison and adjunctions are reused.

## Returned points repaired

RETURN 1 (H2/H4): the item no longer adds `prop-exc-base-change-proper` or
`prop-trf-scheme-galois-comparison` to stmt_deps merely for plain constructions. The
new definition node owns χ and the transparent proper/open interface. The coefficient
instance is supplied directly using the requested `letI`. Existing mathematical proof
dependencies and their imports are retained. No mathematical statement changes.

RETURN 2 (H13): use the return's alternative of reaching `finiteTorConstructible`
through a node this delivery owns. The new composition module publicly imports
`FiniteTorAmplitude` and defines `finiteHorizontalFiniteTorConstructible` as a transparent
alias to its exact intrinsic predicate. K uses that alias. The `def-weil-finite-tor-amplitude`
record is no longer modified; NW's module, declaration and all consumers are retained.

## Second reading by Q07

The repaired packet was reread against the return. The theorem's hypotheses and both
conclusion clauses are unchanged. The χ helper is now owned by the new definition node;
its proper/open comparison is a direct published construction, and coefficient finiteness
is supplied by the explicit `letI` from `Padic.finite_coefficientExtensionRing`. The
finite-Tor dependency record is retained, while the intrinsic predicate is accessed
through the delivery-owned node. The square orientations, conjugate σ direction, unit order, associators, empty
and zero cases, identity and non-flat finite maps, and positive levels including `n = 1`
were checked again. No statement correction or disputed assertion is needed.
