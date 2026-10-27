## Worker report

The module `Sheaf.Paper.ConcreteIntegralProjectionCone` states
`WeilConjectures.ConcreteIntegralProjection.concreteIntegralProjectionCone`, with
one postponed proof. Its definitions give the actual source and target reduction
comparisons, the signed cone comparison, and its canonical derived counit version.
Their data are explicit composites of published constructions; none contains sorry.
The natural-language statement, proof and dependency lists are unchanged.

Hypotheses and objects:

- `D : FiniteFieldDatum.{u}` retains the characteristic, finite field and fixed
  algebraic closure. `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p` give the prime.
  `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]` and
  `[FiniteDimensional (Padic l) E]` give the finite extension. The coefficient
  rings are the existing `Padic.coefficientExtensionRing l E (n+1)`; their definition
  uses the chosen uniformizer and valuation ring, without choosing new ones.
- `Ω` and its `IsAlgClosure (Padic l) Ω` instance unpack the fixed coefficient
  closure needed by the operation datum. `r`, `hr : 1 ≤ r` retain any finite stage
  of `SixFunctorOperationDatum D { l := l, different := hl, Qbar := Ω } E r hr`.
  This is the operation datum, never `SixFunctorDatum`. It contains no assumed
  projection-formula invertibility. The explicit tensor models `aX`, `aZ`, `aY`
  are normalized K-flat presentations of the existing ordinary derived tensor;
  they are not new tensor functors with unconstrained comparisons.
- `[X.Over (Spec (.of D.k))]`, the analogous Y instance, and
  `LocallyOfFiniteType` plus `QuasiCompact` on their structure morphisms express
  finite type over k. No separatedness of either structure morphism is assumed.
  `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` are
  precisely the separated finite-type k-morphism hypotheses.
- `c : Compactification f` is fixed throughout all reductions. `K` and `L` belong
  to `sfIntegralConstructibleCategory`; `_hL : finiteTorConstructibleIntegral ...`
  adds L's uniform finite-Tor condition. No finite-Tor condition is assumed on K.
- S and T are the existing `SfProEtaleProjection.completedSource` and
  `completedTarget`. The latter uses completion of `ordinaryInner`, the published
  presentation of completed tensor with completed pullback. The arrow is exactly
  `(SfProEtaleProjection.integralMap ...).hom`: inverse source completion unit,
  the proper-counit/open projection composite, then compact support of the inner
  completion unit. Its typing theorem `integralDomains` supplies completion and
  constructibility only; its projection-invertibility theorem is not invoked.
  The published `sfQcqsCompactSupportRealization` identifies the ambient proper/open
  `PurCompactSupport.image (completed l E) c` used here with the recorded Roos
  compact-support functor, for every constructible integral input.

Conclusions, in their Lean order:

- The first six conjuncts are `finiteTorConstructibleIntegral` for K, completed
  pullback L, the completed inner tensor, compact support K, S and T. This predicate
  includes `sfIntegralConstructible` (derived completeness, constructibility at
  every positive reduction, and one finite cohomological interval independent of
  the level) and one ordered finite Tor interval independent of the level. Thus
  all five objects named in the node have every required property, and arbitrary
  K has the asserted uniform finite-Tor reductions. The finitely many intervals
  can be enlarged to one common interval if desired.
- `finiteArrow ... n` is `Arrow.mk (finiteReductionProjection ...)`, evaluated at
  `scalarReductionDerivedExtension` of the actual K,L. Its endpoints are the
  finite ordinary tensor/support and support/tensor/pullback objects.
- `ordinarySourceComparison` is tensor reduction and compact-support reduction;
  `sourceComparison` first reduces the inverse source completion unit.
  `ordinaryTargetComparison` is compact-support, tensor and pullback reduction;
  `targetComparison` first inverts the reduced target completion unit. The
  existential h asserts that this actual unit is invertible, not that an arbitrary
  endpoint map exists. The two `IsIso` clauses assert these canonical comparisons
  are isomorphisms. The equality `red.map u ≫ targetComparison = sourceComparison ≫
  finiteArrow.hom` computes reduction of the specified map, without detecting an
  equality of integral maps from their reductions.
- For every distinguished triangle `Triangle.mk u g d`, the cone C satisfies
  `sfIntegralConstructible`. For every distinguished cone triangle of the finite
  projection, the theorem gives an isomorphism of the reduced triangle with that
  triangle. Its first two components are exactly `sourceComparison` and
  `targetComparison`; this includes the identification of derived objects and all
  three triangle arrows. `reductionShift` transports the canonical shift structure
  along `finiteReductionIso`; it does not choose a new exact functor.
- The final existential gives ONE flat-term K-flat map `v : P ⟶ Q` representing
  the actual u under eP,eQ, and eC identifies its signed mapping cone with C.
  `derivedConeComparison` is the reduction of eC inverse followed by the universal
  derived scalar-extension counit, quotient factorization, and signed cone
  comparison. Its `IsIso` clause supplies the finite derived cone identification.
  `restrictedDerivedConeComparison` expresses the same computation after exact
  restriction using the recorded representative comparison. Its invertibility and
  the equation with `sfDerivedReductionTransition` and `Q.map coneTransition`
  retain the actual canonical derived quotient transitions, as well as maps.
  The last equality gives the strict cochain version: quotient maps act on both
  summands and commute with `coneComparison`. The single v, for every level,
  supplies compatible finite cone models. Other cones are compared by the triangle
  isomorphisms above; no functorial cone in a bare triangulated category is assumed.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `FiniteFieldDatum.CoefficientDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its imported coefficient constructions.
- `Sheaf.Paper.SixFunctorOperationDatum`:
  `WeilConjectures.SixFunctorOperationDatum`, with its integral normalization.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`, its specified
  projection, comparison preservation and scalar cocycle interfaces.
- `Sheaf.Paper.QcqsCompactSupportRealization`:
  `WeilConjectures.sfQcqsCompactSupportRealization` and its normalization spec.
- `Sheaf.Paper.SfIntegralConstructible`:
  `WeilConjectures.sfIntegralConstructible` and `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`:
  `WeilConjectures.finiteTorConstructibleIntegral` and imported Tor predicates.

The specified maps reuse `SfProEtaleProjection.integralMap`, `integralDomains`,
`ordinaryInner`, `completedSource`, `completedTarget` from the published
`SfProEtaleProjectionFormula` module; `finiteReductionProjection` from
`ProjectionFiniteReduction`; and `PurCompactSupport`'s completed coefficients,
`image`, `pull`, `finiteReductionIso`, `scalarTensor`, `scalarPull`, and `comparison`.
These definitions are used without invoking the projection-formula assertions in
those modules. No duplicate integral arrow or finite projection is introduced.
The proof imports are the recorded residue-Tor, operation preservation, finite
Krull dimension, prescribed compact-support reductions, basic coefficient reduction,
triangulated constructibles, derived change of rings, K-flat resolution and map
factorization, K-flat homotopy closure and unrestricted reduction-tower modules.
The Mathlib triangle-morphism criterion and derived category are imported directly.
The proof docstring follows all five DAG proof steps and names their tools.

Edge cases checked against the definitions: K=0, L=0, the empty source, and identity f
are allowed; there is no nonzero, nonempty, dominance or positive-dimension binder.
Index n=0 is exponent 1 and includes the residue quotient. All n≥1 in the node occur
as n+1, including every adjacent quotient transition. The characteristic exclusion
is explicit. Schemes need not have separated structure morphisms. All section
variables and the universe u are declared, with both auto-implicit options disabled.
The small pro-etale sites retain their existing object/morphism universes; no new
site encoding or universe equality is imposed. Cone choices are arbitrary and the
comparison is a derived triangle isomorphism, not only cohomological isomorphisms.

Searches for an exact existing statement (no exact match):

- `msearch.py leanfinder`, query “Derived complete integral compact support projection
  map has complete constructible cone and its reductions are finite projection maps”:
  eight unrelated `Profinite.NobelingProof` results.
- `msearch.py leansearch`, query “Derived complete integral compact support projection
  map reduces to the finite coefficient projection map and its cone is complete”:
  eight profinite index/limit cone results, none this statement.
- `msearch.py loogle`, query `Triangle, Functor.mapTriangle`: zero results because
  unqualified Triangle was unknown; the exact qualified Mathlib declaration was
  subsequently read directly in `CategoryTheory/Triangulated/Functor.lean`.
- `msearch.py grep`, `projection.*[Cc]one|[Cc]one.*projection` in CategoryTheory:
  ten unrelated categorical limit-cone results; in Algebra/Homology: six generic
  mapping-cone projections, none about complete constructible coefficient reduction.
- `rg` searches for the item id and concrete integral projection/cone names in
  `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`: no exact
  theorem. Searches for integral projection and finite reduction found the canonical
  map constructions listed above, which are reused. Direct Mathlib source reads found
  `mappingCone.mapHomologicalComplexIso`, `Functor.mapTriangle` and the third-vertex
  isomorphism criterion, none of which states this node.

No statement dispute, node correction, new node or dependency replacement is needed.

A follow-up qualified Loogle query `CategoryTheory.Functor.mapTriangle` returned
12 hits: the triangle functor, its identity/composition/rotation comparison
isomorphisms and triangulated functor API. These generic tools are reused, and
none is an exact instance of the integral projection/cone assertion.

## Second reading by Q85

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
