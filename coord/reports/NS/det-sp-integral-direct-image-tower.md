## Worker report

The delivered module `Sheaf.Paper.IntegralDirectImageTower` states
`AlgebraicGeometry.ProEtale.IntegralDirectImageTower.integral_direct_image_tower`.
There is one postponed theorem, whose docstring follows all eight proof steps of
the node. Every helper definition has real data. No node statement is corrected.

The parameter `Presentation` packages the existing coefficient-tower, reduction,
and geometric-operation interfaces; it adds no hypothesis on a scheme, morphism,
or complex. Its fields are `SpCoefficientTowersAbelian`, `SpReductionTower`, and
`SpTowerShriek.Base` / `SpTowerShriek.Operations`. Their section, restriction,
transition, tensor, and derived universal-property normalizations are retained.
The presentation also retains the dependency's `OpenExchange` and `Laws` witness.
The theorem works with every such presentation and supplies the normalized
reduction geometry, open-mate invertibility, and total-derived-limit interface
itself; none is added as a hypothesis on f, M, or K.

Hypotheses, in the order of the node:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Any finite extension of Q_l: `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The existing coefficient-extension integers,
  uniformizer, and ell-power quotient rings are reused. Ell is not identified with
  a uniformizer; ramified extensions are included.
- Positive characteristic p different from ell: `(k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]`. No algebraic closedness or
  finite-field hypothesis is imposed.
- Separated finite-type k-schemes: `X.Over (Spec (.of k))`, the analogous Y
  instance, and `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on their
  structure morphisms. The morphism has `[f.IsOver (Spec (.of k))]`.
- Smooth pure relative dimension d: `(d : ℕ) [SmoothOfRelativeDimension d f]`.
- A compactification is the existing `Compactification f`, with its actual open
  immersion, proper map, and factorization equation. It is universally quantified.
- M and K in Dbc: `M : Constructible l E X`, `K : Constructible l E Y`.
  This abbreviates the recorded `ConstantModelBoundedConstructible`, not the
  different upstream arbitrary-matrix constructibility predicate.

Coefficient and category conventions:

- `Integral` is the ordinary unbounded derived category of internal modules over
  `condensedRingObj (spIntegralCondensed l E) T`, the pulled-back condensed integral
  ring. `sectionEquivalence` is the recorded exact internal/section-module
  equivalence. There is no discrete constant O_E substitution.
- `red` is that equivalence followed by the recorded `SpReductionTower.red`.
  `level` is its exact derived evaluation. Index `n : ℕ` means exponent `n+1`,
  so every positive exponent occurs.
- `towerShriek` is the existing sequence-site `SpTowerShriek.F`, conjugated by
  the recorded sectionwise derived realization. It is an actual functor on
  D(Tow), not an operation on isomorphism classes of levels.
- `shriek` is precisely `rightDerivedLowerShriekOfCompactification`, namely
  separately derived proper pushforward after exact open extension. `pull` is
  the existing total derived module pullback and `tensor` the existing relative
  K-flat tensor over the pulled-back ring.

Clauses of the conclusion:

1. `spNormalizedConstructibleTorTowers ... (imageTower ... M.obj)` gives
   level constructibility, common cohomological and Tor bounds, and invertibility
   of every canonical derived reduction map, including equal-index maps.
   For every `a b : ℤ` with `torAmplitudeIn _ a b M.obj`, the
   subsequent universal quantifier over n asserts
   `Scheme.HasProEtaleTorAmplitude ... (imageLevel ... n) a (b + 2 * d)`.
2. `restrictedTower` uses the recorded actual strict semilinear transitions
   (`spCompletedTransition`), restricting each coefficient action to the integral
   section ring before taking `Limits.lim`. `Limit` specifies its total right
   derived functor by `IsRightDerivedFunctor`, its computation on K-injectives,
   and the tensor/restriction adjunction. The ordinary unit is normalized on local
   tensor generators, and the derived adjunction is normalized on complexes.
   The reconstruction arrow is defined as the normalized completion unit followed
   by derived limit of `towerBaseChange`. The latter is a constructed map: the
   transpose of the integral proper counit under `o.geometry c.g`, followed by
   proper pushforward of the inverse transpose of the integral open unit under
   `o.openOp c.i`. Thus reconstruction does not consume a free isomorphism.
   The theorem asserts `IsIso (reconstruction ...)`. It also supplies a natural
   whole-tower iso whose hom equals this specific map on every constructible M.
   `finiteComparison` is a definition containing `SpTowerShriek.Fcomparison`,
   transported using the derived sectionwise evaluation and realization counit.
   The level clause is `IsIso (finiteBaseChange ... M.obj n)`: this named morphism
   is evaluation of the constructed tower map followed by `finiteComparison`.
   Both integral endpoints are explicitly in the recorded Dbc.
   Compactification independence is a family of natural isomorphisms on Dbc,
   with identity, cocycle, and normalization by every common dense boundary
   refinement using the existing `compactificationRefinementComponent`.
3. The pullback clause explicitly gives Dbc membership of the uncompleted
   derived pullback. The output `q.pullback f` supplies its strict reduction
   comparison, fixed on ordinary tensor generators and K-flat representatives.
   `pullbackLevelComparison` evaluates that comparison and uses the published
   `Geometry.pullEvaluation` to identify its finite reductions with the finite
   pullback of each K reduction. This is a named constructed iso, so the clause
   needs no bare `Nonempty` witness. The two projection endpoints are explicitly in Dbc.
   `properProjection` is the existing proper counit projection mate at j_!M.
   `compactOpenProjection` is proper pushforward of the open-unit projection
   mate, preceded by the actual compactification pullback compositor. Both
   arrows to their common middle object are asserted invertible. Thus the
   formula is their specified span, not an arbitrary isomorphism of endpoints.

Dependency declarations used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the standing scheme conventions and `compactificationOverField` signature;
  the supplied compactification itself is `AlgebraicGeometry.Compactification`.
- `Sheaf.Paper.CompletedCondensedCoefficients`: `completedCondensedIntegral`
  and the normalized integral coefficient comparison. The general finite-extension
  presentation used here is already supplied by `SpReductionTower.coefficient`.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientTowers`,
  `spCoefficientRing`, `spEllIdeal` and their actual quotient transitions.
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`:
  `SpCoefficientTowersAbelian`, with exact evaluation and scalar models.
- `Sheaf.Paper.SmoothPurityReductionTowerNormalized`: `SpReductionTower`,
  `spIntegralCondensed`, `spIntegralModuleEquivalence`, `spIntegralSectionModules`.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `ConstantModelBoundedConstructible`, `constantModelBoundedConstructible`.
- `Sheaf.Paper.SmoothPurityNormalizedTowers`:
  `spDerivedCoefficientEvaluation`, `spNormalizedConstructibleTorTowers`.
- `WeilConjectures.Compactification.Refinement`:
  `Compactification.Refinement` and the category of compactifications.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  total derived pullback, `derivedUpperStarLowerStarAdjunction`, and
  `leftDerivedUpperStarComp`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` / `.Tensor`:
  `CondensedRing.derivedTensor`, the existing relative K-flat derived tensor.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`.
- `Sheaf.Paper.SmoothPurityTowerShriekLevels`: `Base`, `Operations`, `F`,
  `finiteF`, `R`, and the normalized strict geometric calculus.
- `Sheaf.Paper.TowerCompactSupportProjectionFormula`:
  `SpTowerProjection.realization` for the exact section-site derived transport.
- `Sheaf.Paper.SmoothPurityTowerReconstruction`:
  `spCompletedEvaluation` and `spCompletedTransition`, fixed on actual sections.
- `Sheaf.Paper.CompactificationCoherenceCocycle`:
  `compactificationRefinementComponent`, used to normalize independence.
- `Sheaf.Paper.ModuleObjectProjectionMap`: `moduleObjectProjectionMap`.
  Its pullback tensorator is the published K-flat-normalized comparison in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`.

All currently stated proof-dependency modules are imported, including the
ringed strict-tower limit, limit/direct-image, open-extension, scalar-change,
K-flat, and tensor-descent interfaces. Unstated proof dependencies are left as
proof work, rather than replaced by assumptions in the theorem.

Edge cases checked against the statement: zero M and K, including reversed Tor
bounds (which force the input to be zero); empty X and Y;
d=0 (no widening); positive level one (index zero); equal reduction indices;
ramified E (ell-power and uniformizer-power filtrations only cofinal);
non-algebraically-closed positive-characteristic k; arbitrary compactification,
including a non-dense one. No nonemptiness or finite-field assumption is added.
All variables and the universe are explicitly bound.

Searches for an existing statement:

- `msearch.py ... leanfinder` with “The integral compactly supported derived
  direct image is the derived inverse limit of its finite coefficient reduction
  tower and satisfies the projection formula”: eight hits, on compactly supported
  integration, condensed colimits and Nobeling exactness; none is this theorem.
- `msearch.py ... loogle '"lowerShriek"'`: zero hits.
- `msearch.py ... grep 'integral.*(shriek|tower)|normalizedTower|compactSupport'
  CategoryTheory`: zero hits.
- `rg` in the upstream WeilConjectures sources and side Sheaf library for
  integral direct-image/shriek/tower/projection names: existing integral model,
  completed-value and separate projection statements were found; none states
  the three clauses for the ordinary pulled-back-condensed module category and
  the recorded normalized strict ell-power tower.
- The exact blueprint-id grep in upstream WeilConjectures and the namespace
  search in `dag/lean_names_upstream.json` found no existing declaration.

Validation uses only the prescribed `scompile.py` and `deliver2.py` wrappers.
No shared source, launcher script, live artifact, or git state was edited directly.

## Repair of returned delivery

The immutable returned head is `0e7a151183f0`. Its H3 defect is real: `iso`,
`finite`, and `baseChange` were unrelated free fields. The saved packet was first
submitted to the required dry run, and this repair retains all unaffected work.

The three free fields are replaced as follows.

- `finiteComparison` is a definition, and its body explicitly composes
  `SpTowerShriek.Fcomparison` with the realization counit and the two exact
  sectionwise evaluation comparisons. There is no selectable finite comparison.
- `ReductionPull.ordinary` is normalized by `generators`: after evaluating and
  transporting to ordinary scalar coordinates, it sends `1 tensor f*(x)` to
  `f*(1 tensor x)`. Here both f*(x) and f*(1 tensor x) are the actual specified
  integral and finite geometric adjunction units on every base-changed test
  object. Scalar linearity, sheafification and generation determine the ordinary
  map, at every strict-tower level. `Evaluation.sections` separately fixes every
  evaluation coordinate map as identity on the underlying section.
- `ReductionPull.derived` is normalized by `representatives`. The equation
  compares its hom with localization of that exact ordinary map, through the
  recorded reduction counit and exact pullback factorization, for every flat-term
  K-flat complex. These representatives resolve every object, so an unrelated
  derived automorphism cannot preserve this normalization.
- `properReduction` and `openReductionInverse` are actual `homEquiv` transposes
  through `s.operations.geometry c.g` and `s.operations.openOp c.i`. The former
  uses the integral counit and the latter the integral open unit. The theorem
  supplies invertibility of the latter as an output, not as a hypothesis.
- `towerBaseChange` composes those two mates. `CanonicalTowerComparison.hom_eq`
  pins its whole hom to this map on each M, including any maps invisible to
  separate evaluations. `reconstruction` directly uses `towerBaseChange`.
- `finiteBaseChange` evaluates this exact map and composes with the defined
  `finiteComparison`. The level conclusion asserts invertibility of that
  morphism; the former trivial `IsIso` of a freely supplied iso and bare
  level `Nonempty` clause are removed.

The advisories are addressed too. `Presentation` now includes the supplied
`OpenExchange`/`Laws` witness. Pullback levels use `pullbackLevelComparison`,
computed from the same normalized strict scalar/pullback comparison and the
published `Geometry.pullEvaluation`, instead of unrelated finite isomorphisms.

All new helpers belong to the item's canonical comparison construction and are
listed in its `lean.declarations`; no independent notion or new DAG node is
introduced. The only postponed theorem remains `integral_direct_image_tower`.
Its existential output now includes the normalized geometry and open-mate
invertibility needed to construct the canonical arrows. The proof docstring's
steps 2, 3 and 6 explain their construction. All new definitions have real data.

Additional searches: LeanFinder query “Canonical comparison between integral
compact support and finite coefficient reduction as the proper counit mate and
open extension unit mate” returned eight generic condensed adjunction hits;
none states this comparison. Mathlib grep `mateEquiv|Fcomparison|leftAdjointUniq`
in CategoryTheory returned the generic mate/uniqueness machinery used here.
Loogle `"mateEquiv"` returned twelve generic mate identities.
Exact-name upstream and side-library searches for `towerBaseChange`,
`ordinaryPullLevelMap`, and `ReductionGeometry` returned no existing declaration.

## Worker self-check

The normalized scalar generator equation covers every n (including n=0), every
scheme morphism and every module; it imposes no smoothness, field, flatness of the
quotient or completeness assumption. Its two sides are in the same finite module
sheaf. The K-flat equation compares arrows of whole strict derived systems,
not only their evaluations. The proper and open mates therefore exist before
bounded-constructible invertibility is asserted. For identity f, both units reduce
to the scalar tensor-unit normalization; for zero M all maps are the zero-object
identity. Ramified coefficients retain exactly the recorded ell-power quotient
maps. The inverse open mate is never substituted by an arbitrary isomorphism.

The theorem's field/scheme/smooth hypotheses, Tor interval, compactification
normalization and projection span are retained from the reviewed packet.
The independent second reading is performed by the maintainer, as specified in
the dispatcher brief; this is the author's self-check, not an independent review.

Initial validation diagnostic (saved packet, before repair): the prescribed dry
run reached server confirmation after a missing local RationalizationKaroubi
artifact, then failed while compiling the transitive dependency
`Sheaf.Paper.DerivedPullbackTensorHom` after 60 seconds. No delivery was pushed.
The repaired source subsequently passed the prescribed `scompile.py` check:
the sandbox module compiled in 57.5 seconds and the library-path module in
54.6 seconds, with no compiler errors or warnings. Both are within the
60-second per-file limit.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
