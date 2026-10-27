## Worker report

The module `Sheaf.AlgebraicGeometry.MarkedFiniteDiagramApproximation` states
`AlgebraicGeometry.exists_marked_finite_diagram_approximation`, with its only theorem
proof postponed by `sorry`. The node's statement and dependencies are unchanged.

I read ILO Expose III section 2, Theorem 5.1, Corollary 5.4 and the end of Proposition
6.2, printed pp. 35--45 (PDF pp. 41--51). The last paragraph models the individual
components and their intersections, applies approximation to preserve regularity and
codimension, and obtains SNC on a neighborhood of the whole special fibre. The preceding
paragraph identifies the dominant reduced part with a disjoint union near that fibre.

Clause-by-clause translation:

* `A`, `[CommRing A]`, `[IsDomain A]`, `[IsNoetherianRing A]`,
  `[HenselianLocalRing A]`, `hA : IsExcellent A` give exactly the excellent henselian
  Noetherian local domain. The maximal ideal is `IsLocalRing.maximalIdeal A`.
* The completed ring is `AdicCompletion (IsLocalRing.maximalIdeal A) A`, with its canonical
  `algebraMap`. All schemes and rings use the same explicit universe `u`.
* `Z : Closeds (Spec (.of A))` is the specified closed subset; only its underlying closed
  subset is used in the node. Pullback supports are `Closeds.preimage` under structure maps.
* `J`, `[SmallCategory J]`, `[FinCategory J]`, `F` specify an arbitrary finite diagram of
  schemes over the completed spectrum. `hF` makes all its objects finite type, using
  `LocallyOfFiniteType` and `QuasiCompact`. The selected objects `x : Fin n → J` are the
  finitely many `X_i`; no injectivity or nonemptiness of this selection is assumed.
  `hX` records their Noetherianity and regularity.
* `H i` is the specified boundary ideal; `hH` uses exactly the published
  `IsStrictNormalCrossingsBoundary`. `hZ` equates its support with the inverse image of Z.
* `r`, `C` enumerate its reduced irreducible component ideals. `hCred` makes those ideals
  radical, `hCdistinct` prevents repetitions, and `hC` says their supports are precisely the
  images of the irreducible components of the boundary subscheme. These are data already
  specified in the node, not extra geometric conditions: finite enumerations exist by
  Noetherianity. Regularity and all expected-codimension conditions of the original
  components follow from the existing boundary predicate, rather than a new SNC predicate.
* `B₀ : Subalgebra A (AdicCompletion ... A)` with `B₀.FG` is an index in the directed set
  of all finite type subalgebras, ordered by inclusion. Thus no arbitrary presentation or
  cofinality hypothesis is introduced. `F₀` models the whole requested finite diagram;
  all its structure maps are finite type. The natural isomorphism `e` identifies its
  canonical completed base change with `F`, including every arrow and diagram equation.
* `C₀` are ideal-sheaf markings on the selected models. Their pullback along the inverse
  of `e.app` followed by the canonical projection is exactly `C`. Sums of these ideals
  are the actual scheme-theoretic intersections, with canonical closed inclusions from
  `IdealSheafData.subschemeFunctor`; thus components, all intersections and all their
  inclusion arrows descend together. The additional clause about each diagram arrow
  `a : j ⟶ x i` asserts that whenever it presents a specified intersection before descent,
  its descended map is a closed immersion with exactly the corresponding sum as kernel.
  This retains compatibility when such intersections are also objects of the extra diagram.
* `N₀` and `1 ≤ N₀` precede the universal quantifiers over all later finitely generated
  subalgebras `B`, inclusions `hB`, exponents `N ≥ N₀`, and `A`-algebra maps `v : B →ₐ[A] A`.
  Congruence means, for every element, its included image minus the completed image of
  its specialization belongs to `(maximalIdeal A ^ N).map (algebraMap A ...)`.
  The specialized model is the pullback of `F₀` along `v.comp (Subalgebra.inclusion hB)`.
  This is canonically the iterated base change to B and then along v; it does not replace
  the prescribed specialization by an arbitrary map.
* `MarkedApproximationNeighborhood` packages the conclusion, using only the existing
  scheme, ideal-sheaf, regularity and SNC notions. Its first clause includes EVERY point
  mapping to `IsLocalRing.closedPoint A`, not just a chosen point or a dense part of the
  fibre. `IsRegularScheme V.toScheme` states regularity of the open neighborhood.
* The scheme-theoretic union of the restricted component markings is their ideal infimum
  `⨅ j, (C j).comap V.ι`. It is SNC by the recorded predicate and its support is exactly
  the inverse image of Z. There is no assumption that a marking remains irreducible after
  specialization; the resulting boundary predicate permits each to split.
* The dominant reduced union is the infimum of vanishing ideals of precisely the GLOBAL
  irreducible components possessing a generic point whose image is generic in Spec A.
  A vanishing ideal supplies the reduced closed structure. This ideal is formed on the
  entire specialized scheme before `comap V.ι`. Its inclusion is already a closed
  immersion; `IsOpenImmersion` asserts the additional open property required in the node.
* The final clause ranges over ALL finite subsets of the original marking labels, says
  their restricted intersections are regular, and states the stalk Krull-dimension equality
  with `s.card` at EVERY point. The empty subset gives the entire neighborhood and
  codimension zero. Empty intersection schemes impose no pointwise dimension conditions.

The two `markedApproximationPullback`/`markedApproximationProjection` abbreviations are
literal applications of Mathlib's `Over.pullback` and `pullback.fst`. The conclusion
predicate is transparent logical packaging of this one theorem's clauses, not a second
definition of any dependency notion. All helpers belong to this node and are listed in
`lean.declarations`; there are no opaque constructions, arbitrary choices, or auxiliary
theorems with unmatched sorries.

Dependency declarations read and used:

* `Sheaf.RingTheory.ExcellentRing`: `IsExcellent` (with its quasi-excellent and universally
  catenary predicates).
* `WeilConjectures.Mathlib.RingTheory.Henselian`: published henselian terminology;
  `HenselianLocalRing` itself is Mathlib's class, extending `IsLocalRing`.
* `Mathlib.RingTheory.AdicCompletion.Algebra`: `AdicCompletion`, its ring/algebra structure
  and canonical `algebraMap` (the dependency record also refers to Basic).
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; its
  quasi-compact companion is `AlgebraicGeometry.QuasiCompact`.
* `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`, namely
  locally Noetherian and stalkwise regular; re-exported by the boundary module.
* `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`, read in full, including the
  component/intersection witness and the empty-subset case.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  `pullback.snd`; `Mathlib.CategoryTheory.Comma.Over.Pullback`: `Over.pullback`.
* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
* `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
* `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`. The boundary's
  radical ideal and the reduced union's vanishing ideal give precisely this reduced
  scheme structure; no separate reduction construction is copied.
* `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`: `IdealSheafData.comap`, its
  `comapIso`, support formula and functoriality; `IdealSheafData.vanishingIdeal` supplies
  the reduced closed structure. I also checked Mathlib's irreducible-component subscheme
  construction: it intentionally is NOT necessarily reduced and is therefore not used
  for the dominant reduced union.

Every recorded proof-dependency module is imported privately. The two unstated graded
approximation/dimension lemmas remain future proof inputs, not assumptions replacing the
conclusion. The eleven DAG proof steps are included in full in the theorem docstring.

Edge cases checked: n=0; an empty extra diagram; repeated selections of X; a field A
(maximal ideal zero); Z empty; Z the whole base (possible only for the boundary cases
actually satisfying the hypothesis); zero component count; empty intersections;
empty closed fibre (V can be empty); no dominant components (the infimum is the unit
ideal, defining the empty closed subscheme); several dominant components; and splitting
of a component marking after specialization. The global-component condition is evaluated
before restriction, as the node explicitly requires. No `Nonempty` assumptions or
independent index universes exclude these cases.

Searches actually run:

* `msearch.py ... leanfinder`: "Finite diagrams of regular schemes with strict normal
  crossings divisors descend from an adic completion and remain regular near the closed
  fibre under sufficiently congruent approximation". Eight hits, principally
  `AffineTransitionLimit` finite-type morphism descent; none states this result.
* `msearch.py ... loogle`: "AlgebraicGeometry.IsStrictNormalCrossingsBoundary,
  AdicCompletion". Zero hits; Loogle does not know the project SNC declaration.
* `msearch.py ... grep`: `marked.*[Aa]pproximation|[Aa]pproximation.*[Bb]oundary|StrictNormalCrossings`.
  Zero Mathlib hits.
* Ripgrep of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the node id and chosen declaration names found no existing statement or name clash.
  Searches for marked diagrams and approximation found unrelated curve spreading and
  perfect-complex approximation modules, not this statement. Mathlib ideal-sheaf and
  finite-category sources provided the canonical constructions used instead of copies.

No statement correction, dependency repair, new DAG node, or disputed assertion is needed.
The first version compiled cleanly with scompile.py; after adding the explicit matching
condition for diagram arrows representing intersections, the complete version is checked
again by scompile.py and the required delivery dry run.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
