## Worker report

The module `lean/Sheaf/AlgebraicGeometry/FiniteRangeComparison.lean` states
`AlgebraicGeometry.Etale.finite_range_exchange_comparison`; its proof is `sorry`, as
required for stage 2.  It restores the declaration recorded before the upstream sync,
using the current `derivedBaseChangeMapPlus` interface and a reduced import list.  The
old import list pulled both the side exact-couple implementation and the upstream
`WeilConjectures.CategoryTheory.ExactCouple`, producing a duplicate declaration.  The
reduced imports use the published truncation-exchange and convergence interfaces and
compile against the current live library.

The theorem renders the node statement clause by clause:

* The explicit binders `{X' X Y' Y : Scheme.{u}}`, `g' : X' ⟶ X`, `f' : X' ⟶ Y'`,
  `f : X ⟶ Y`, `g : Y' ⟶ Y`, and `sq : IsPullback g' f' f g` are the cartesian square
  and its four displayed morphisms.  `sq.toCommSq` is the commutative-square witness
  used by the canonical derived exchange map.  This is the exact pullback witness
  encoding used by the corrected node interface.
* `K : _root_.DerivedCategory.Plus
  (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})` is an arbitrary bounded-below
  complex of étale abelian-group sheaves on `X`; no torsion or constructibility
  hypothesis is added.
* `(a b : ℤ) (_hab : a ≤ b)` renders the integer interval and its order.  The
  hypothesis `_hK : ∀ q : ℤ, q < a ∨ b < q → IsZero
  ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K)` says exactly that every
  cohomology object outside `[a,b]` vanishes.
* `_h₂ : ∀ p q : ℤ, IsIso (tE
  (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q)` renders the
  isomorphism hypothesis on every E2 component.  `tE` is the recorded truncation-couple
  map on the layer `H^q(K)[-q]`, and `derivedBaseChangeMapPlus` is the canonical
  abelian-coefficient exchange transformation.
* The existential conclusion supplies exact couples `P` and `Q` in the sheaf category
  on `Y'`, identifies their `D` and `E` terms and all three structure maps with the
  recorded truncation couples `truncationPhi f g` and `truncationPsi g' f'`, and supplies
  limiting subobjects `L`, `M`.  The map `z` between limiting cycles and `tInf` between
  page-infinity terms are quantified for every `(p,q)`.  The first displayed equation
  is the exchange comparison after the `hPE`/`hQE` identifications; the second is the
  limiting cokernel square; the final conjunct gives `IsIso (tInf p q)` for all indices.
* The next conjunct states `IsIso` on the induced cohomology map in every degree `n`.
  The final conjunct states `IsIso` on the natural-transformation component itself,
  which is the corrected generic abelian-coefficient form of the node's consequence.

Dependency declarations used:

* `Sheaf.AlgebraicGeometry.ChosenCartesianSquare` records
  `AlgebraicGeometry.ChosenCartesianSquare`, the chosen cartesian-square notion behind
  the square dependency; the theorem uses its exact `IsPullback` witness and
  `sq.toCommSq`.
* `Sheaf.AlgebraicGeometry.DerivedCategories` supplies the étale derived-category
  encoding and the `DerivedCategory.Plus`/homology API recorded for
  `def-weil-pbc-derived-categories`.
* `Sheaf.AlgebraicGeometry.TruncationExchangeCouple` supplies
  `CategoryTheory.TruncationExchange.D`, `.E`, `.alpha`, `.f`, `.g`, `.tE`, and
  `AlgebraicGeometry.Etale.truncationPhi`/`truncationPsi`.
* `Sheaf.CategoryTheory.ExactCoupleConvergence` supplies
  `CategoryTheory.BigradedExactCouple`, `LimitSubobjects`, `pageInfinity`,
  `limitBoundary_le_cycle`, and the limiting cokernel API.
* `WeilConjectures.SixFunctors.BaseChange.Derived` supplies
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`.

Edge cases checked: `a` and `b` are arbitrary integers subject only to `a ≤ b`;
cohomology may vanish identically, including the zero object and degrees `n < a`;
`K` is arbitrary in `D+`, including the zero complex; all `(p,q)` and `n` are globally
quantified, including negative indices; no nonempty scheme, nonempty index set,
torsion, smoothness, properness, or coefficient-ring finiteness is introduced.  The
empty scheme and degenerate pullback square are allowed by the scheme and `IsPullback`
binders.

Searches made:

* `msearch.py Q39 sbc-lem-finite-range-comparison leanfinder "spectral sequence
  comparison E2 isomorphism finite range abutment"`: eight generic homology/total
  complex hits; no convergent spectral-sequence comparison theorem.
* `msearch.py Q39 sbc-lem-finite-range-comparison loogle
  "CategoryTheory.BigradedExactCouple, LimitSubobjects, pageInfinity"`: zero hits;
  the service reported the namespace identifier as unknown.
* `msearch.py Q39 sbc-lem-finite-range-comparison grep
  "BigradedExactCouple|pageInfinity|derivedBaseChangeMapPlus" Mathlib`: zero hits.
* `rg` over the read-only `WeilConjectures/` source and project `lean/Sheaf/` found
  `derivedBaseChangeMapPlus` and the exact-couple/truncation infrastructure but no
  declaration of `finite_range_exchange_comparison`; searching the item id likewise
  found no upstream duplicate.
* The node's existing stage-1 Mathlib searches were also checked: no Mathlib
  spectral-sequence abutment-comparison match exists.

No new nodes, dependency repairs, statement correction, or `STATEMENT-DISPUTED` flag
are needed in this delivery.  The corrected generic exchange expression is already
recorded in the node's `statement_change`; this module preserves that statement.

## Earlier second reading (a previous round; superseded)

I reread the node, its five statement dependencies, and the complete theorem signature.
The square, coefficient category, bounded-below object, interval bound, outside-range
vanishing, and every-index E2 isomorphism hypothesis appear exactly once.  The
existential exact-couple data matches the node's `\varphi_\infty` clause through the
specified `z` restriction and quotient square, and the two final `IsIso` conclusions
match the cohomology and derived exchange consequences.  The only source-sync change
is the import repair documented above; no mathematical hypothesis or conclusion was
changed.  `scompile.py` compiled the module both in the private overlay and against the
library with no errors or warnings beyond the expected `sorry` declaration warning.

## Second reading by Q39

I independently opened the sandbox node, the complete Lean signature, all five
statement-dependency records and their declarations, the current proof-dependency
records, and the source blueprint lemma and its enclosing remark. The mathematical
signature is correct and I left it verbatim unchanged. The following is my inventory
of the statement, with the Lean rendering and verdict for each item.

| Object, hypothesis, or conclusion in the node | Lean rendering and verdict |
| --- | --- |
| Four schemes and the displayed four arrows | `{X' X Y' Y : Scheme.{u}}`, `{g'}`, `{f'}`, `{f}`, `{g}` have exactly the displayed endpoints. Pass. |
| Cartesian square with its specified commutativity | `sq : IsPullback g' f' f g` and `sq.toCommSq`. Pass: an `IsPullback` witness gives the canonical isomorphism to the chosen fibre product with both projection equations. Conversely the recorded `ChosenCartesianSquare.isoPullback`, `hom_fst`, and `hom_snd` give this pullback witness. No different square or extra geometric property is assumed. |
| Abelian coefficients and arbitrary bounded-below K | `K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`. Pass: this is the abelian-sheaf case explicitly described in the derived-categories dependency, not its separate module-coefficient or torsion predicate. |
| Integers a <= b | `(a b : ℤ) (_hab : a ≤ b)`. Pass. |
| H^q(K) vanishes outside [a,b] | `_hK : ∀ q : ℤ, q < a ∨ b < q → IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj K)`. Pass: the disjunction is exactly the complement of the closed integer interval. |
| Phi = g inverse image after Rf pushforward | `truncationPhi f g`, opened at its definition: `lowerStar.rightDerivedFunctorPlus ⋙ upperStar.mapDerivedCategoryPlus`. Pass. |
| Psi = Rf' pushforward after g' inverse image | `truncationPsi g' f'`, opened at its definition: `upperStar.mapDerivedCategoryPlus ⋙ lowerStar.rightDerivedFunctorPlus`. Pass. |
| The canonical derived exchange, and not an arbitrary transformation | `derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq`. Pass: I read the source definition, its underived-resolution characterization and its source/target functors. It is the recorded exchange dependency. |
| The E2 comparison induced by exchange is invertible for every (p,q) | `_h₂ : ∀ p q : ℤ, IsIso (tE ... K p q)`. Pass: `layer K q` is H^q(K)[-q], and `tE` applies H^(p+q) to exchange on this layer. The recorded `pageIso`, `truncationSourceIso`, `truncationTargetIso` and the last clause of `truncation_exchange_couple_morphism` identify it with precisely the node's degree-p exchange on H^q(K). There is no assumption on unrelated maps. |
| The specified two truncation exact couples | Existential `P Q`, both D equalities, both E equalities, and all six `HEq` equalities for alpha, f and g. Pass: these are all ten identifications of the recorded couples, not merely couples with matching page objects. |
| The limiting comparison is the one induced by exchange | `L : LimitSubobjects P`, `M : LimitSubobjects Q`, globally indexed `z`, `tInf`, the cycle-inclusion equation and the cokernel equation. Pass: I read `LimitSubobjects.Z_glb/B_lub` and `pageInfinity`, which is the cokernel of limiting-boundary inclusion into limiting cycles. Monicity makes the cycle restriction unique and epimorphic cokernel projections make the quotient map unique. The `hPE/hQE` transports have the correct directions. |
| Every infinite-page component is invertible | `∀ p q : ℤ, IsIso (tInf p q)` inside the same existential data. Pass: both limiting data sets are selected before all bidegrees, as required. |
| Every cohomology map of exchange is invertible | The separate conjunct `∀ n : ℤ, IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map (... .app K))`. Pass: it uses the same exchange component, not a separately chosen abutment isomorphism. |
| Consequently exchange itself is invertible | Final `IsIso ((derivedBaseChangeMapPlus ... sq.toCommSq).app K)`. Pass. |

Source and inherited correction: the blueprint lemma, order 1436, assumes finite
cohomological range and E2 isomorphisms and concludes abutment and derived-exchange
isomorphisms. Its proof explicitly uses E-infinity comparison and induction along
finite filtrations. The enclosing remark discusses smooth base change, but the
comparison lemma is the generic implication; it does not assume smoothness, qcqs,
torsion, a finite ring, or invertibility of torsion orders. I also read Stacks
`derived.tex`, `lemma-two-ss-complex-functor` (015J), including its left-exact-functor,
abelian-category and bounded-below hypotheses, and `homology.tex`,
`lemma-characterize-strict` (0127). These agree with the convergence and finite
filtration steps; no geometric hypothesis is hidden in those steps.

Before comparing the Lean, I checked the existing NV `statement_change` against this
source. It replaces the ill-typed monoidal `baseChange Ab` spelling by the canonical
generic abelian `derivedBaseChangeMapPlus`, without changing the mathematical map or
any hypothesis/conclusion. I opened both recorded citers. For
`sbc-thm-bounded-derived-smooth-base-change`, its current proof Step 4 applies precisely
the bounded-below abelian exchange conclusion and then the plus/unbounded compatibility
node: `holds: true` is correct. For `sbc-thm-bounded-allowable-torsion`, the abelian
exchange conclusion is likewise preserved: `holds: true` remains correct as a
compatibility verdict. Its current active dependency list no longer cites this item
(the id survives in older metadata), so the two-entry historical audit is not a new
correction or a claim that it still has two active citers. This delivery changes
neither the natural-language statement nor its inherited correction record.

Edge cases: `a = b`, negative a/b, n = 0 and negative n, zero K, identically zero
cohomology, empty schemes, identity arrows and degenerate Cartesian squares are all
allowed. There is no nonempty index-set hypothesis; every (p,q) lies in ℤ x ℤ. The
universe u is arbitrary, and abelian groups use the site's established u+1 size
convention. No independent coefficient field, characteristic restriction, extra
category instance, boundedness of the pushforward endpoints, or torsion assumption
is imposed. The source's bounded-below condition is exactly `DerivedCategory.Plus`.
`autoImplicit false` and the explicit `universe u` leave no unbound variable or universe.

Independent searches (2026-10-17):

- LeanSearch through `msearch.py`, query "A morphism of spectral sequences that is an
  isomorphism on E2 induces isomorphisms on finite filtered abutments": eight hits on
  short-complex homology, quasi-isomorphisms and the abelian four lemma; no match.
- LeanFinder through `msearch.py`, query "bounded cohomology comparison morphism
  hypercohomology spectral sequence isomorphism abutment": eight group-cohomology
  low-degree isomorphism hits; none states this implication.
- Loogle through `msearch.py`, query `CategoryTheory.SpectralSequence.Hom`: nine hits
  on the morphism structure, its components and compatibility; no abutment theorem.
  The earlier quoted-string combined query failed to parse and is not counted as
  evidence of absence.
- `rg` on Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`, using
  `finite_range_exchange_comparison`, spectral/abutment/comparison combinations,
  and the node id. Mathlib has no matching theorem. I opened the project hits
  `complex_spectral_sequence_comparison` (directed colimits with explicit convergence
  hypotheses) and `spectralSequence_page_induction` (page comparison, without this
  geometric abutment conclusion); neither states this node.
- The shared and current-server `FiniteRangeComparison` source is an earlier copy
  of this very node's module, with the same signature but its obsolete conflicting
  import closure; the base node has an empty `lean` record. This delivery restores
  that withdrawn module's usability and binding in place. It does not introduce a
  second declaration or treat an unbuildable archived source as an existing match.

Mismatches found and repaired:

1. The first worker's import list still named the retired
   `Sheaf.AlgebraicGeometry.DerivedCategories`, although the dependency now records
   `WeilConjectures.AlgebraicGeometry.DerivedCategories`. I read the current module
   using `scompile.py --source` and changed this import to the recorded owning module.
2. The reduced imports had discarded all proof dependencies. I restored ordinary
   proof-only imports for `ExactCoupleMorphism`, `DerivedCoupleFunctoriality`,
   `FiniteFiltrationInduction`, and `DerivedGeometricStalkConservative`. The couple
   construction and exchange dependency are already public imports.
   `lemma-weil-pbc-exact-couple-abutment` currently has no recorded Lean declaration,
   so its withdrawn module is not imported. `HypercohomologyFiltrations` uses the
   separate unbounded API and its old conflicting exact-couple import closure;
   the signature instead uses the recorded D+ truncation declarations directly.
   No private copy of its image filtrations or its couples is added here.
3. The old proof docstring still cited `lem-sp-page-induction`, whereas the current
   node's proof uses direct induction in the exact-couple page API and
   `lem-sp-derived-couple-functoriality`. I updated steps 1–3 to carry that current
   proof, including transports, the global versus degree-specific choices, finite
   cycle/boundary transport, and uniqueness of the limiting quotient map.
4. I restored the standard copyright header. No theorem signature, object,
   mathematical hypothesis, conclusion, node statement, or dependency record changed.

There are no new nodes or dependency modules to review. The file defines no data and
contains exactly one theorem with exactly one whole-proof `sorry`; no new hollow
definition or proof was introduced. Source/blueprint docstrings and the 100-character
line convention pass. The recorded `lean.statement` is verbatim the file signature.
The repaired module compiled independently in both wrapper modes (sandbox and library
path), with no errors and no warnings, within the unchanged 60-second per-file limit.
