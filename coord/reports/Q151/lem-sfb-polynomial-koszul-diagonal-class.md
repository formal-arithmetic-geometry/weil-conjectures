## Worker report

Stage 2 delivery: `Sheaf.Algebra.Homology.PolynomialKoszulDiagonalClass`, declaration
`AlgebraicGeometry.polynomial_koszul_diagonal_class`. Its sole theorem has proof `sorry`.
The two supporting definition modules construct all data explicitly or define predicates;
no definition chooses data from this theorem or from a bare existence assertion.
No statement correction or dependency replacement is made. The item statement and accepted
stage-1 proof plan are unchanged. Q116's PASS was a stage-1 split review, not a Lean delivery:
the current node has no `lean`, and the queue lists stage 2. The inherited stage-1 live-wins
BLOCKED ending therefore does not apply to this stage-2 task (brief-stage2 section 0).

Clause-by-clause rendering:

* Commutative Noetherian R, flat finitely presented R-algebra B: the binders of
  `PolynomialKoszulDiagonalAssignment` are `[CommRing R] [CommRing B] [Algebra R B]`,
  `[IsNoetherianRing R] [Module.Flat R B] [Algebra.FinitePresentation R B]`.
  Module flatness is exactly flatness of the algebra map by `RingHom.flat_algebraMap_iff`.
  No separate Noetherian B, nonzero ring, properness, smoothness, domain, regularity,
  lci, global dualizing pair, or diagonal-perfectness hypothesis is imposed.
* A fixed polynomial presentation is an instance of `PolynomialKoszulChart` with
  `P = MvPolynomial (Fin n) R`, identity coordinates and localization element 1.
  The chart record also covers the expressly requested finite localizations, using
  `IsLocalization (Submonoid.powers h)` along its specified coordinate map.
  `quotient` is an R-algebra map and `surjective` is its surjectivity.
  Finite simultaneous localization can be encoded by the product of the elements.
* L = Omega^n[n]: `PolynomialKoszulChart.top` is the existing exterior power of
  `KaehlerDifferential R P`. `volume` is the ordered exterior product of `D (X i)`.
  `coefficient` is its single complex in degree -n. `coefficientShiftIso` identifies
  this with the usual degree-zero module shifted by n using `singleFunctors.shiftIso`.
* C is `C.model`, literally `(ModuleCat.derivedCoinduction p).obj C.coefficient`;
  the action is the recorded precomposition B-action of coinduction.
  A = B tensor_R B, first-factor C_1 = `C.firstPullback`, using the existing
  `relativeDualizingModuleFirstPullback` and K-flat scalar extension.
  The diagonal is the existing `relativeDualizingModuleDiagonal` for multiplication.
* T = P tensor_R B_2, q and e are `graphQuotient` and `graphEvaluation`.
  `graphEquations` are exactly x_i tensor 1 minus 1 tensor bar(x_i).
  `graphKoszul` reuses `ExteriorAlgebra.koszulComplex`, extended by
  `ComplexShape.embeddingDownNat`; no second Koszul differential is introduced.
* The graph coefficient line is the actual scalar extension `graphTop`, and
  `graphCoefficientMap` is the adjoint mate of the ordinary unit. Differential
  base change identifies this line with top differentials over B_2.
* The specified kappa is `PolynomialKoszulDiagonalDatum.kappa`; `normalized` is
  `IsKoszulDiagonalNormalization`. This predicate requires beta with its exact
  extended-evaluation counit equation, invertible scalar/restriction and coefficient
  maps, and a graph trace. It requires kappa to equal the displayed composite of
  coinduction applied to beta, `koszulDiagonalCoinductionComp`, and the graph trace.
  Transitivity is constructed by `Adjunction.comp` and `rightAdjointUniq` from the
  existing adjunctions, fixing its composite evaluation counit.
* `IsKoszulDiagonalGraphTrace` expresses the top-wedge normalization without
  selecting an arbitrary rank-one generator: the actual graph augmentation is
  required quasi-isomorphic and sends the degree-zero unit to 1; the top cocycle
  sends the ordered graph wedge to the ordered differential volume. The derived
  equation identifies that cocycle with the adjunct of the inverse trace. Thus
  the trace sends dual(top graph wedge) tensor volume to 1, using the standard
  cochain differential and shift signs. Normalizations are equations, not hypotheses
  asserting an arbitrary isomorphism would have the desired property.
* The class is `C.diagonalClass kappa`, the inverse coinduction hom-equivalence applied
  to kappa.inv, preceded by the canonical restriction/single-complex comparison.
  The `multiplication` field requires `IsIso (relativeDualizingModuleClassMap ... xi)`.
  That existing map is curry of diagonal multiplication followed by xi into ordinary
  module derived internal Hom; this is the node's multiplication-by-xi conclusion.
* For every R -> R' with R' Noetherian, scalar change is the pushout clause of
  `KoszulDiagonalChartChange.IsAdmissible`; its quotient pushout encodes B' and P'.
  The target flatness and finite-presentation binders are inherited algebra properties
  of those pushouts, not extra restrictions on the source map. There is no flatness
  binder on the base or ambient maps. Tensor-product and arbitrary pushout models
  are both allowed. Coordinates and their order are preserved; the volume condition
  fixes the top differential map (the top line is generated by the ordered volume).
* `IsComparison` is the evaluation-counit coinduction comparison, with its explicit
  scalar/restriction mate equation and ordinary differential mate. The `change` field
  provides such an isomorphism and `PreservesClass` requires the derived class square.
  `diagonalRing` applies the ring map on both tensor factors. The diagonal comparison
  is the scalar mate of b:B->B', with its formula on every element; it is required
  invertible as a conclusion. The first-pullback comparison is constructed from the
  scalar-extension adjunctions and c. These equations specify the actual pullback of xi.
* `identity` compares with `koszulDiagonalExtensionId`, and `composition` compares
  successive scalar maps with their composite under `koszulDiagonalExtensionComp`.
  Both canonical identifications use uniqueness of left adjoints to restriction.
  No arbitrary identity or transitivity isomorphism is introduced.
* Localized ambient charts use the same graph normalization. Simultaneous localization
  is the second `IsAdmissible` clause, requiring localization of P at h and B at p(h)
  and an isomorphic base. Its diagonal-ring map localizes BOTH factors. The first
  clause covers base localization as a scalar change. Ambient localization at h with
  p(h) a unit has B'=B (localization at that unit), so is included too.
* A polynomial refinement is `KoszulDiagonalRefinement`: it specifies P[t] as a ring
  by an equivalence preserving P and t, the inclusion and evaluation t->a, old and new
  coordinates with the new coordinate last, the dimension n+1 and quotient factorization.
  `IsContraction` uses the connecting morphism of the actual two-term resolution for
  multiplication by t-a; the quotient top-form map sends the new ordered volume to
  the old volume. Since the old wedge times d(t-a) is the new ordered volume, this
  is exactly dual(t-a) tensor d(t-a)->1, with the new differential last.
* `modelMap` pastes the two evaluation counits with this coefficient contraction.
  `refinement` requires preservation of xi, invertibility of the model map and equality
  with the maps from every other lift for the same charts. `refinement_change` gives
  the scalar/localization square for these actual maps. `KoszulDiagonalRefinementPath`
  is an identity or ordered finite composite of normalized one-variable comparisons;
  `iterated` says the composites agree. Thus the iterated and scalar coherence clauses
  concern the specified maps, not arbitrary isomorphisms of the endpoints.

The theorem asserts existence of one such compatible assignment. This packages the node's
specified graph construction together with all its universally quantified compatibility
clauses, rather than assuming a dualizing pair or postulating independent generators.

Dependency declarations read and reused:

* `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
* `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, `RingHom.flat_algebraMap_iff`;
  `Mathlib.RingTheory.Flat.Basic`: `Module.Flat`.
* `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
* `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`, `X`, `aeval`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`,
  `singleFunctor`, `singleFunctors`; the module categories use the existing small
  derived localization instance, without adding a universe equality on any site.
* `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction`:
  `ModuleCat.derivedCoinduction`, `derivedCoinductionAdjunction`, and their
  K-injective/evaluation interfaces. All transitivity and scalar mates use this adjunction.
* `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `D`,
  `linearMapEquivDerivation`; `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic` and
  `.ExteriorPower.Basic`: `exteriorPower`, `exteriorPower.ιMulti`.
* `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`; the existing closed `ihom`
  used by `relativeDualizingModuleClassMap` is its curried presentation.
* `Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison`:
  `relativeDualizingDerivedExtension`, `relativeDualizingModuleDiagonal`,
  `relativeDualizingModuleFirstPullback`, `relativeDualizingModuleClassMap`.
  Only its constructed ordinary-module helpers are used, not its theorem's proper/
  geometric input or a supplied global dualizing pair.
* `WeilConjectures.AlgebraicGeometry.KoszulComplex`:
  `ExteriorAlgebra.koszulComplex`, the single recorded Koszul construction.
* Additional Mathlib category APIs: restriction/extension of scalars and its ordinary
  adjunction, `mapDerivedCategoryFactors`, adjunction uniqueness/composition,
  `IsPushout`, `IsLocalization`, `ShortComplex.ShortExact.singleδ`.

Already stated proof dependencies are imported without `public`: total tensor signed
coherence, algebraic shriek relative perfectness, coinduction total Hom model, flat
polynomial quotient perfectness, differential base change/localization, flatness and
exactness of localization. The remaining graph-coinduction, perfect exchange,
polynomial-refinement and Koszul evaluation-pasting proof nodes currently have no
recorded module; their proof obligations are preserved verbatim in this theorem's
proof docstring. They are proof dependencies only, not unstated objects required to
type this statement. Their canonical objects/maps have been explicitly supplied here.

Edge cases checked: n=0 uses the empty graph wedge and degree-zero coefficient; B=0
and R=0 are allowed throughout; h=1 is the unlocalized polynomial chart; h=0 is allowed
only with the resulting zero localization, as it should be. Identity changes and nonflat
base maps (e.g. Z -> Z/pZ for R-flat B) are included. P is finite free relative to R
before localization, but B is never assumed perfect over its diagonal tensor algebra.
No characteristic, residue-field, reducedness or regularity restriction is present.
All variables and universes are explicitly bound; autoImplicit is disabled.

Searches (all before creating the new notions):

* msearch LeanFinder: “Koszul normalized polynomial diagonal generator of relative
  dualizing complex compatible with arbitrary scalar extension” returned eight
  cotangent presentation/basis maps, no match. The followup ordered-graph query
  returned cotangent and representation standard-complex facts, no match.
* msearch LeanSearch: “A canonical Koszul normalized diagonal generator system with
  coinduction evaluation mates and localization compatibility” returned ordinary
  normalization, localization and exact-pairing facts, no match. The final coherent
  scalar-change localized-chart query returned eight unrelated localization and
  representation facts, no match. Exact outputs are recorded in the new nodes.
* msearch Loogle: `ModuleCat.derivedCoinduction, AlgebraicGeometry.algebraicShriek_relative_perfect`
  reported unknown project identifier; `KaehlerDifferential, exteriorPower` reported
  unknown `exteriorPower`. These failures are recorded honestly, not claimed as matches.
* msearch grep: `diagonal.*[Cc]lass|graph.*[Cc]oinduction|[Cc]oinduction.*graph`
  returned matrix diagonal results only; `Koszul.*[Dd]iagonal|[Dd]iagonal.*[Kk]oszul`
  returned zero hits.
* `rg` in the project, upstream library and DAG for `PolynomialKoszulChart`,
  `KoszulDiagonalSystem`, and `koszulDiagonal`: no existing notion. Searches for graph
  coinduction and diagonal classes found the existing coinduction and polynomial
  diagonal RHom reduction but no graph-normalized class or its compatibility system.
  `blueprint_refs.py search 'Koszul diagonal'` found zero nodes; `ancestor` returned None.
  The latest blueprint direct-images proof was read; the node is a supporting algebraic
  prerequisite, not a unit statement.

Sources read: local Stacks dualizing.tex at 0E2E, 0BZI's top-differential canonicalization
footnote, 0BZJ's evaluation-variable refinement and Tor-independent scalar exchange;
0A70/0A71's coinduction adjunction. The scalar compatibility here is the node's explicit
additional construction, not misattributed as a verbatim Stacks assertion.

Validation: all three files compiled separately in dependency order with scompile.py
against the live server build; no errors or warnings other than permitted sorry warnings.
The required dry-run and delivery wrapper are run after this report and node records.

## New nodes

`def-sfb-polynomial-koszul-diagonal-data` owns the localized polynomial charts, ordered
graph Koszul trace normalization, scalar mate comparisons, diagonal class and changes,
evaluation refinements, their two-term coefficient contraction, and finite refinement
paths. It follows 0E2E's graph algebra diagram, 0BZI's top-differential normalization,
0BZJ's evaluation variable, and the item's explicit compatibility construction. Searches
above found no such combined notion. Existing differentials, exterior powers, Koszul
complexes, derived coinduction, scalar extension and multiplication maps are reused.
The new definition node asserts no theorem and introduces no hollow data.

`def-sfb-polynomial-koszul-diagonal-system` owns the datum of graph-normalized classes
with invertible multiplication, its assignment over all flat finitely presented
Noetherian-base algebras, and the precise compatibility predicate (changes, identity,
composition, lift-independent refinement, iterates, scalar/refinement square). It also
constructs the canonical identity and composite scalar identifications by adjunction
uniqueness. This is the missing predicate needed to state the item's entire conclusion;
its source and all comparisons are those just listed, with no existence theorem hidden
in its definitions. The same searches found no existing system notion. The theorem of
the assigned item, and only that theorem, asserts existence of this system.

## Second reading by Q151

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
