## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteRangeComparison` states
`AlgebraicGeometry.Etale.finite_range_exchange_comparison`. Its sole theorem has
`by sorry`; it introduces no definitions and proves nothing.

Hypotheses and objects, clause by clause:

- The four schemes and arrows are the explicitly bound `X' X Y' Y`, `g' f' f g`.
  `sq : IsPullback g' f' f g` is the Cartesian square, in the same form used by
  the recorded truncation-couple interface. A chosen pullback identification
  supplies this witness, and a witness supplies the canonical pullback identification;
  exchange depends only on `sq.toCommSq`.
- `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u+1})`
  is exactly a bounded-below derived abelian sheaf; no module coefficients or
  torsion, smoothness, qcqs or cohomological-dimension hypotheses are imposed.
- `(a b : ℤ) (_hab : a ≤ b)` binds the finite interval, and `_hK` says
  `IsZero` of the cohomology sheaf whenever `q < a ∨ b < q`.
- `truncationPhi f g` and `truncationPsi g' f'` are the recorded composites
  g inverse image after Rf pushforward and Rf' pushforward after g' inverse image.
  The transformation is the recorded `derivedBaseChangeMapPlus` at the square.
- `_h₂` asserts `IsIso (tE ... K p q)` for every pair of integers. Here `tE`
  is cohomology of exchange on H^q(K)[-q]. The recorded `pageIso`,
  `truncationSourceIso`, `truncationTargetIso`, and clause (3) of
  `truncation_exchange_couple_morphism` identify this very arrow with
  g inverse image R^p f_* H^q(K) -> R^p f'_* g' inverse image H^q(K).
  Thus this is the E₂ hypothesis, including negative indices, with canonical
  identifications rather than an arbitrary comparison map.

Conclusions, clause by clause:

- The existential `P Q` have exactly `D`, `E`, `alpha`, `f`, and `g` of the
  recorded two truncation couples, specified by equality or heterogeneous equality.
  These introduce the couples mentioned in the prose; they add no assumptions.
- `L : LimitSubobjects P` and `M : LimitSubobjects Q` specify the limiting
  cycles and boundaries by their greatest-lower-bound/least-upper-bound properties.
  `pageInfinity` is their quotient, the recorded E-infinity notion.
- The equation for `z` identifies it with the restriction of the original
  `tE` to limiting cycles, transported by `hPE` and `hQE`. The quotient equation
  with `cokernel.π` uniquely characterizes `tInf` as its induced map on E-infinity.
  Thus the witnesses cannot be unrelated isomorphisms of objects. The conjunct
  `∀ p q, IsIso (tInf p q)` states the infinite-page conclusion in every bidegree.
  The induced map is unique by monicity of the cycle inclusions and epicity of
  the quotient projections, so existentially presenting it loses no conclusion.
- `∀ n, IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map (...app K))`
  is exactly the isomorphism on every abutment, on the actual exchange component.
- The final `IsIso (...derivedBaseChangeMapPlus...app K)` is the derived exchange
  isomorphism. The formerly ill-typed alternative master notation was corrected
  as described below; no coefficient category was substituted.

Dependencies used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`, whose
  Cartesian data correspond to the `IsPullback` witness used by the couple API.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the recorded Mathlib `DerivedCategory.Plus`
  and its `homologyFunctor`, with abelian-sheaf coefficients as its docstring specifies.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`.
- `Sheaf.AlgebraicGeometry.TruncationExchangeCouple`: `TruncationExchange.D`, `E`,
  `alpha`, `f`, `g`, `tE`, `Etale.truncationPhi`, `truncationPsi`, and the
  canonical page identifications explained above. Its existing theorem supplies
  the exactness and morphism properties for the future proof.
- `Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`: the three recorded
  hypercohomology filtrations, especially sequences (2) and (3); the actual
  D+ truncation-couple encoding is supplied by the preceding dependency, as its
  record instructs. No representative complex or torsion hypothesis is needed.
- `Sheaf.CategoryTheory.ExactCoupleConvergence`: `LimitSubobjects`, `pageInfinity`,
  and `limitBoundary_le_cycle`, reused directly, without redefining convergence.

The stated proof-dependency modules are imported without `public`: ExactCoupleMorphism,
SpectralSequencePageInduction, FiniteFiltrationInduction, TruncationExchangeAbutment,
DerivedGeometricStalkConservative.
The docstring carries all mathematical steps of the corrected node proof.

Edge cases checked: K = 0, the empty scheme, a = b (one possibly nonzero
cohomology sheaf), negative a and b, n < a, and negative p or q. All are admitted
by the binders and full integer quantifiers. No boundedness of either output is
assumed. The coefficient universe is u+1 on the small etale site of Scheme.{u},
as required by the published six-functor API. The E₂ assumption includes zero
terms; an arrow between zero objects is an isomorphism, so these cause no restriction.

Searches made:

- msearch.py leanfinder: "For an etale cartesian square, finite cohomological range
  and isomorphism of E2 hypercohomology exchange maps imply isomorphism of the
  derived base change map". Eight unrelated etale algebra/base-change results;
  no exact declaration.
- msearch.py loogle: `CategoryTheory.SpectralSequence, IsIso`. Zero hits;
  the service reported unknown identifier IsIso.
- msearch.py grep: `finite.*range.*comparison|spectral.*comparison` in
  Mathlib Algebra/Homology. Zero hits.
- rg over the project and upstream for `finite.range|finite_range` and this node id:
  found upstream `Etale.isIso_baseChange_app_of_isGE_of_isLE` in
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived`. Read its complete
  docstring and signature: its coefficients are ModuleCat Λ and its sole conclusion
  is the baseChange component being an isomorphism. It does not state the required
  abelian-coefficient infinite-page and abutment assertions, so it is not an exact match.
- rg over Mathlib Grp and the project for AddCommGrpCat monoidal/tensor structures:
  the Cartesian structure is not a tensor/monoidal-closed flat-resolution package.
  This confirms the compiler's failure of the final master notation, rather than
  supplying any excuse to add stronger coefficient hypotheses.

Validation for this repair uses the prescribed scompile.py local side-project
overlay and deliver2.py --no-push, without overriding wrapper settings.

## Statement corrected

The old statement's final sentence asserted
`IsIso ((Etale.baseChange Ab sq.toCommSq).app K)` in the master notation.
The unchanged old statement is preserved verbatim in `statement_change.old_statement`.
The server rejects that expression: `failed to synthesize MonoidalCategory AddCommGrpCat`.
Reading MorphismDefs shows that this API additionally requires a symmetric monoidal
closed, monoidal preadditive coefficient category with functorial flat resolutions.
Its generic abelian replacement already exists: the dependency's canonical
`Etale.derivedBaseChangeMapPlus`. The final notation now names that declaration;
every mathematical object, hypothesis, and isomorphism conclusion is retained.
The obsolete sixth proof step identifying the unavailable master component is removed;
its full old proof is preserved in `statement_change.old_proof`. The now-unused `def-weil-pbc-derived-inverse-image` proof dependency is removed;
`statement_change.old_proof_deps` preserves the original list verbatim. The source blueprint order 1436 asserts BC(K) is an isomorphism and
does not prescribe the ill-typed master expression. This changes no unit statement.

All citers found by examining both dependency fields across dag/nodes:

- `sbc-thm-bounded-allowable-torsion`: holds true. It uses the abelian exchange
  isomorphism, which is unchanged by the corrected Lean name.
- `sbc-thm-bounded-derived-smooth-base-change`: holds true. Its finite-range
  comparison step uses the same exchange isomorphism; no hypothesis changes.

No citer is edited. No new definition node or dependency replacement is needed.

## Earlier second reading (a previous round; superseded)

I read the corrected statement first against blueprint order 1436, including its
proof paragraph. It asserts E2 comparison implies infinite-page and abutment
comparison and then invertibility of BC(K), with no smoothness, torsion or finite
cohomological-dimension assumption. I also read Stacks homology.tex,
lemma-characterize-strict (Tag 0127): its ambient hypothesis is an abelian category
and its objects have finite filtrations. These are proof ingredients, not extra
geometric hypotheses. The correction retains precisely the abelian exchange of
its recorded dependency. I opened master MorphismDefs.lean: its baseChange uses
the monoidal coefficient package, whereas the recorded generic
BaseChange.Derived.derivedBaseChangeMapPlus supplies the abelian transformation.
The old statement is preserved verbatim. I checked both citers and their proof
steps: bounded-allowable-torsion uses the abelian abutment/exchange conclusion;
bounded-derived-smooth-base-change uses it after forgetting module coefficients.
Both uses survive this notation correction; the module-coefficient bridge is
still required in the latter theorem, exactly as before the correction. The two
recorded holds:true verdicts are valid. A scan of both dependency fields found
no other citers.

Object/hypothesis/conclusion inventory and individual verdicts:

1. Four schemes and the four oriented arrows: `{X' X Y' Y : Scheme.{u}}`,
   `{g' : X' ⟶ X}`, `{f' : X' ⟶ Y'}`, `{f : X ⟶ Y}`, `{g : Y' ⟶ Y}`.
   Verdict: exact. `sq : IsPullback g' f' f g` expresses the Cartesian square.
   I opened ChosenCartesianSquare: its isoPullback and two projection equations
   are the chosen pullback identification. That identification uniquely exists
   for this IsPullback witness; neither exchange nor its conclusion depends on
   additional choice data. Using the recorded couple API's witness loses no case.
2. Bounded-below abelian-sheaf complex K: the explicit `DerivedCategory.Plus`
   binder on `Sheaf X.smallEtaleTopology AddCommGrpCat.{u+1}`. Verdict: exact.
   I opened DerivedCategories and its coefficient convention; no module, ring,
   torsion, or finiteness instance has been substituted.
3. Finite cohomological interval: `(a b : ℤ) (_hab : a ≤ b)` and `_hK` asserting
   `IsZero` of homologyFunctor at every `q < a ∨ b < q`. Verdict: exact closed
   interval and the same quantifier order.
4. Phi, Psi and the canonical exchange: I opened the recorded D+, E, alpha, f,
   g, tE, truncationPhi, truncationPsi and page-identification declarations in
   TruncationExchangeCouple, and derivedBaseChangeMapPlus in BaseChange.Derived.
   The two composites are exactly inverse image after derived pushforward and
   derived pushforward after inverse image. Verdict: exact canonical arrow.
5. E2 hypothesis: `_h₂ : ∀ p q : ℤ, IsIso (tE ... K p q)`. Here tE applies
   H^(p+q) to exchange on H^q(K)[-q]. The recorded pageIso, source and target
   isomorphisms and the final clause of truncation_exchange_couple_morphism
   identify it with the node's degree-p exchange. Verdict: exact; no arbitrary
   map hypothesis and no hidden nonnegative-degree restriction.
6. The two truncation couples: existential P/Q with their D/E equalities and
   HEq alpha/f/g fields reproduce all recorded structure maps. Verdict: exact
   witnesses for the couples already introduced in the node, not extra input.
   HypercohomologyFiltrations was opened too: sequences (2)/(3) are these same
   functor images of truncations, with the D+ interface supplied by the recorded
   truncation-couple dependency, rather than its older unbounded representatives.
7. Infinite-page conclusion: L/M are LimitSubobjects of those couples. I opened
   their signatures: Z_glb/B_lub force the actual limiting cycles/boundaries;
   pageInfinity is their cokernel quotient. The first equation forces z to be
   the restriction of the very tE from hypothesis 5; the second forces tInf to
   be its quotient map. The cycle inclusion is mono and cokernel projection is
   epi, so no unrelated isomorphism can satisfy these equations. The universal
   `IsIso (tInf p q)` is therefore precisely the required induced infinite-page
   comparison in every bidegree. Verdict: exact.
8. Abutment conclusion: `∀ n : ℤ, IsIso ((...homologyFunctor _ n).map
   (...derivedBaseChangeMapPlus...app K))`. Verdict: the actual exchange's
   cohomology map in every degree, not merely isomorphic abutment objects.
9. Derived conclusion: the final `IsIso (...derivedBaseChangeMapPlus...app K)`.
   Verdict: exactly the corrected node's exchange component. No output
   boundedness is assumed and no extra conclusion was added.

Edge cases: K=0, empty schemes, a=b, a or b negative, n=0, n<a, and negative
p/q are all covered by the explicit binders. Empty nonzero support is allowed
by _hK even though a≤b chooses a nonempty enclosing interval. There is no index
set requiring Nonempty, and no characteristic restriction. The single scheme
universe u and coefficient universe u+1 agree with the small-etale site and
published six-functor signatures; arbitrary u is bound explicitly. I checked
all parameters and universes with autoImplicit false and the verbatim signature.

Independent searches used different phrasing from the worker:

- LeanFinder: “An isomorphism on the second page of a bounded hypercohomology
  spectral sequence induces isomorphisms on its limiting page and cohomology
  abutments.” Eight generic complex homology/quasi-isomorphism hits; no match.
- Loogle: `CategoryTheory.SpectralSequence`. Twelve structural/page/functor
  declarations, no theorem with this exchange and abutment conclusion.
- LeanSearch: “A comparison of bounded hypercohomology spectral sequences which
  is an isomorphism on E2 induces isomorphisms on abutments.” Service unavailable
  (Internal Server Error); no mathematical verdict taken from that failure.
- msearch grep: `abutment.*comparison|comparison.*abutment`, zero hits.
- Direct rg on Mathlib Algebra/Homology, project Sheaf, and upstream
  WeilConjectures for finite-range and spectral comparison terms. I opened
  Etale.isIso_baseChange_app_of_isGE_of_isLE: it uses ModuleCat Λ and concludes
  only the derived isomorphism, omitting this node's infinite-page/abutment
  assertions. The generic exact-couple/page-comparison lemmas are ingredients,
  not duplicates. No exact existing statement was found.

No mismatch requiring a Lean or node edit was found. The worker's correction
is justified and I left it unchanged. No new node or dependency module is part
of this delivery. The inherited truncation-couple record explicitly documents
its separate existing projection/boundary construction issue; this delivery
introduces no definition or choice and does not conceal or duplicate that data.
The sole theorem remains `by sorry`, its source/blueprint docstring contains
all five proof steps, and all Lean lines are at most 100 characters. The node's
lean.statement equals the file signature verbatim. Server scompile.py passed
with nice 19, two threads and 60 seconds per file (FiniteRangeComparison: 1.9 s),
without errors or warnings. Second reading changed only this review report.

## Returned-delivery repair

The immutable-head review returned a mismatch between `proof_deps` and the
union of the five corrected proof steps' `uses`. The removed sixth step was the
only user of `def-weil-pbc-derived-inverse-image`. Removed that stale dependency
and its proof-only ExactFunctor import; preserved the original dependency list
verbatim in `statement_change.old_proof_deps`. The sorted dependency list now
equals the union of `uses` exactly. The Lean signature and mathematical statement
are unchanged. This repair does not claim a new independent second reading.

## Second reading by NV

This is a fresh independent reading after the returned-delivery repair. I read the
corrected natural statement first against the full source at blueprint order 1436,
then its Lean rendering. The blueprint's proof explicitly includes the infinite-page
comparison as well as every abutment and BC(K). Stacks homology.tex,
lemma-characterize-strict (0127), assumes an abelian category and finite filtered
objects; it adds no geometric, torsion, or cohomological-dimension hypothesis to
this comparison. The cited filtration source has a torsion hypothesis, but its
construction does not use it: this item explicitly uses the general truncation
couples, not its torsion-specialized specification theorem.

Inventory, with the Lean rendering and individual verdict:

1. Objects: four arbitrary schemes and four oriented arrows f:X→Y, g:Y'→Y,
   f':X'→Y', g':X'→X. The first two binder lines render these exactly. The binder
   `sq : IsPullback g' f' f g` renders the Cartesian identification. I opened
   ChosenCartesianSquare: its isoPullback and projection equations encode the
   same universal property; that identification is unique as a square. Verdict:
   exact objects and Cartesian hypothesis, no additional geometric restriction.
2. Object: K in D+ of abelian sheaves on X's small étale site. The explicit
   `DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`
   binder is precisely this. I opened DerivedCategories and its listed Mathlib
   coefficient convention. Verdict: exact, with no ring/module substitution.
3. Hypotheses: integers a≤b, cohomology zero outside the closed interval [a,b].
   `(a b : ℤ) (_hab : a ≤ b)` and `_hK`, using `q < a ∨ b < q` and
   `IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj K)`, render every
   clause with the same quantifiers. Verdict: exact.
4. Objects: Phi, Psi, and canonical exchange. I read the actual definitions of
   truncationPhi/truncationPsi and derivedBaseChangeMapPlus. They are Rf_* then
   exact g inverse image, exact g' inverse image then Rf'_*, and the canonical
   derived descent of the underived exchange. Its resolution characterization
   and shift compatibility confirm the actual exchange arrow. Verdict: exact.
5. Hypothesis: every E2 comparison on H^q(K) is invertible. `_h₂ : ∀ p q : ℤ,
   IsIso (tE ... K p q)` uses cohomology of exchange on the layer H^q(K)[-q].
   I read layer, tE, pageIso, truncationSourceIso, truncationTargetIso and the
   page-identification clause of truncation_exchange_couple_morphism. Their
   conjugations identify this very map with the degree-p exchange in the node.
   Verdict: exact canonical comparison, including negative indices.
6. Conclusion: invertibility on every infinite-page component. The P/Q
   witnesses have exactly the dependency's D/E and alpha/f/g fields; the HEq
   clauses transport the structure maps without relaxing them. I read
   LimitSubobjects and pageInfinity: the GLB/LUB conditions force the actual
   limiting cycles/boundaries, and the page is their quotient. The equation
   with `(M.Z p q).arrow` forces z to be the restriction of the original tE;
   the equation with `cokernel.π` forces tInf to be its induced quotient map.
   Monicity and epicity make both arrows unique. `∀ p q, IsIso (tInf p q)`
   therefore states exactly the induced infinite-page assertion. Verdict: exact.
7. Conclusion: every abutment map is invertible. The `∀ n : ℤ, IsIso` clause
   applies homologyFunctor to the actual derivedBaseChangeMapPlus component.
   Verdict: all degrees of the specified exchange, without output boundedness.
8. Conclusion: exchange itself is invertible. The final IsIso uses the same
   component on K. Verdict: exact corrected statement and source conclusion.

I also opened HypercohomologyFiltrations and the recorded truncation-exact-couples
node. The latter explicitly directs consumers to the D+ interface used here,
rather than the representative-complex/unbounded interface. Its known inherited
projection/boundary construction defect is already recorded for maintainer repair;
this delivery adds no definition, choice, or alternative construction. There are
no new nodes or dependency modules in this delivery.

Correction audit: MorphismDefs.lean requires MonoidalCategory, MonoidalPreadditive,
SymmetricCategory, MonoidalClosed and HasFunctorialFlatResolution for its master
baseChange. The general abelian exchange does not require that package and is
already the recorded dependency. Replacing the untypable final spelling preserves
all mathematical hypotheses and conclusions. I opened both citers and their proof
steps. Bounded-allowable-torsion uses precisely the abelian abutment and exchange
conclusions. Bounded-derived-smooth-base-change uses the same finite-range step
via underlying abelian coefficients; its coefficient bridge is still necessary,
as before the correction. Both holds:true verdicts remain correct. Scanning both
dependency fields found exactly those two citers; no unit statement changes.

Edge cases: zero K (empty cohomological support), empty schemes, a=b, negative
interval endpoints, n=0, n<a and all negative p/q are admitted. No external
index set, characteristic, smoothness, torsion, qcqs or finiteness instance occurs.
The universe u is explicit, and AddCommGrpCat.{u+1} agrees with the small-site
and published functor sizes; no additional universe equality is imposed.

Independent searches in this reading:

- LeanFinder: "bounded cohomology spectral sequence second page comparison
  implies invertible exchange and limiting quotient maps". Eight group
  cohomology/homology hits, no exact match.
- Loogle: `CategoryTheory.SpectralSequence.Hom`. Nine structural declarations,
  no exchange/convergent-abutment comparison theorem.
- msearch grep: `abutment.*IsIso|IsIso.*abutment|finite_range_exchange`. Zero hits.
- Direct rg in Mathlib's spectral-sequence directory, project Sheaf and upstream
  WeilConjectures for comparison/finite-range terms. I opened upstream
  Etale.isIso_baseChange_app_of_isGE_of_isLE: it uses ModuleCat Λ and concludes
  only invertibility of baseChange, without the infinite-page and abutment
  clauses. Generic spectral comparison lemmas are ingredients, not this full
  statement. No exact existing declaration found.

No remaining mismatch was found, so I preserved the Lean and node. The earlier
returned repair correctly removes the obsolete proof-only import and dependency;
the current proof_deps is exactly the union of the corrected proof steps' uses.
The sole theorem has only `by sorry`; there are no delivered definitions, local
notation or private declarations. The docstring contains the source/blueprint and
all five proof steps. The signature matches lean.statement verbatim, every Lean
line is at most 100 characters, and every variable/universe is explicitly bound.
Prescribed scompile.py passed both sandbox and library-file checks (2.2/2.4 s)
without errors or warnings. This second reading changes only this report.
