## Worker report

Item: `lem-coef-simplicial-interval-localization`. The module
`Sheaf.CategoryTheory.SimplicialIntervalLocalization` states
`CategoryTheory.CoherentNerve.simplicial_interval_localization`, with its sole proof `sorry`.
The other six declarations are definitions belonging to this statement's own notation.
All their data are real expressions; there is no choice of data from an unproved existence
assertion. In particular `intervalProjection` uses the inverse of a specified isomorphism.
No other DAG node is stated and no node statement or dependency list is changed.

Source read: [Higher Algebra](https://www.math.harvard.edu/~lurie/papers/HA.pdf),
Proposition the project server, printed p. 110, and its proof on printed pp. 113–114;
Notation the project server and Proposition the project server on printed pp. 112–113.
Also read the current blueprint ancestor
`sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`,
paragraph 2. The statement is the interval-localization foundation for its derived
coefficient-adjunction step, as explained in the DAG's ancestor record.
There is no repair note for this item.

The clause-by-clause correspondence is as follows.

- A small simplicial category is `A : CoherentNerve.SCat.{u}`. This is the existing
  bundled Mathlib enrichment, not a newly axiomatized category. Its ordinary category
  is exactly `CoherentNerve.underlying A`, whose arrows identify with mapping vertices
  under `SimplicialCategory.homEquiv'`. Enlarging the common universe `u` includes all
  object and mapping sizes of the input. Test targets use `max u w` and the prescribed
  degreewise `SSet.uliftFunctor.{w}`, so targets can have any larger size.
- The class `W` is `MorphismProperty (underlying A)`. `hiso` says every ordinary
  isomorphism belongs to `W`. The three implications in `hcomp` are precisely
  two-out-of-three for composable arrows, including closure under composition.
- The chosen interval object of every `x` is `I x`; `h x : Δ[1] ⟶ hom A x (I x)`
  is its universal path. `intervalTranspose` is the actual curry of
  `(h x ⊗ₘ 𝟙 _) ≫ eComp SSet x (I x) y`. Thus it is composition with `h`, not an
  unrelated isomorphism of the two mapping objects. The hypothesis `htensor` says this
  actual map is an isomorphism for all `x,y`. Naturalness in `y` is automatic for this
  formula by the enrichment's associativity, so no additional hypothesis is necessary.
  Mathlib's internal hom has precisely the function-complex simplices stipulated in
  the node. The left argument in the curry is the interval, as required by Mathlib's API.
- `intervalProjection A I h x` is the ordinary arrow corresponding to the vertex
  obtained by first applying the existing constant-diagram map to the identity vertex,
  then applying the inverse of `intervalTranspose A I h x x`. This is precisely the
  transpose of the constant identity path. `hp` says it lies in `W` for every `x`.
- The replacement is an arbitrary `B : SCat.{u}` and enriched functor `r : A ⟶ B`.
  `hobjects` identifies the object types, and `hr` says its object map is the identity
  (using heterogeneous equality to avoid a hidden transport choice). `hkan` is local
  Kan fibrancy and `hweak` is the recorded realization-based weak homotopy equivalence
  on every mapping object. No functorial replacement of all simplicial categories is
  required, and no Kan assumption on `A` is imposed.
- `nerveFunctor.obj B` is exactly `N_hc(B)` from the recorded dependency, so it is the
  node's `D`. The conclusion supplies `θ` together with `IsIntervalNerveMap r θ`.
  This is a fully specified canonical map, not an unconstrained comparison: in every
  degree its objects are `r` of the objects of the input string, and each entire
  enriched mapping map is the constant simplicial map at `r` of that string's composite.
  These formulas determine every enriched functor, hence every simplex of `θ` uniquely.
  They state exactly the discrete-enrichment map followed by `r`, including identities
  and higher simplices. Existence of this specified map is included in the statement;
  no definition chooses it from an unproved mere-existence theorem.
- `intervalOrdinaryMarking A W` is exactly the set of one-simplices `mk₁ f` with `W f`.
  `intervalCoherentMarking W θ` is exactly their images under `θ`. By the previous
  full simplex characterization, these are the coherent edges corresponding to `r(w)`;
  no homotopy saturation or extra edges are added to `V`.
- `intervalInvertingDiagrams K V E` applies the dependency's `fullSubcomplex` to the
  internal functor object, with vertex predicate saying the corresponding actual
  simplicial map sends each marked edge to `Enhanced.IsEquivalenceEdge E`.
  The use of the existing `Functor.natTransEquiv` and `SSet.unitHomEquiv` decodes a
  functor vertex into that actual map. All transformations, including noninvertible
  transformations, and all higher simplices between these vertices remain present.
- The universal quantifier over `(E : SSet.{max u w}) [SSet.Quasicategory E]` is the
  node's arbitrary infinity category. `restriction` runs from the `V`-inverting full
  functor subcategory of `D` to the `W`-inverting full subcategory of `N(C_0)`.
  Its equation with the two inclusions identifies it exactly with
  `(MonoidalClosed.pre (SSet.uliftFunctor.{w}.map θ)).app E` on all simplices.
  `Enhanced.IsFunctorEquivalence restriction` is precisely the requested equivalence.
  This is the primary full-functor-category formulation of the node; its displayed
  equivalence of infinity localizations is explicitly an equivalent reformulation,
  not a second independent clause or an assumption on a chosen localization model.
- There is no model-category assumption, no original-mapping-space fibrancy hypothesis,
  and no tensor other than the one interval tensor. The theorem docstring contains all
  seven DAG proof steps, with their named dependencies.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CoherentNerveComparison`: its recorded
  `CategoryTheory.coherent_nerve_comparison` and
  `CategoryTheory.CoherentNerveComparisonStatement`, read with their docstrings and
  fields. Its public infrastructure gives `CoherentNerve.SCat`, `underlying`, `hom`,
  `IsLocallyKan`, and `nerveFunctor`; these exact definitions are used here.
  The underlying Mathlib `SimplicialCategory`, `EnrichedCategory`, and
  `SimplicialNerve` source signatures and conventions were inspected too.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsEquivalenceEdge`,
  `fullSubcomplex`, `constantDiagrams`, `IsWeakHomotopyEquivalence`, and
  `IsFunctorEquivalence`, read with their full definitions and docstrings. These
  implement precisely the node's edge equivalences, full subcategories, spaces,
  and functor equivalences. There are no private copies of these notions.
- The stated proof dependencies are imported without `public`:
  `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus` and
  `Sheaf.CategoryTheory.HammockInfinityLocalization`.
  `lem-coef-enriched-marked-realization` has no Lean record yet, so its module cannot
  be imported. It remains a proof dependency named in the docstring; it is not a
  missing statement dependency and is not restated here.

Edge cases checked mathematically before fixing the signature:

- Empty object set: all interval and replacement conditions have their correct
  vacuous meanings; the canonical nerves are empty and the functor categories from
  them have their usual terminal behavior. No `Nonempty A` is assumed.
- Discrete enrichment: `I x = x` with the constant identity path recovers the
  ordinary/coherent nerve identification. Mapping sets can be empty, in particular
  for reversed intervals; the canonical-map predicate quantifies over actual paths
  and never chooses an element in an empty mapping object.
- Terminal and identity-only examples: `p`, both endpoints, and marked identity edges
  are retained. Degenerate simplices are included, and `n = 0` in the canonical-map
  predicate specifies the image object and its identity mapping map.
- Taking all arrows in `W` is permitted; taking only isomorphisms still imposes the
  interval-projection condition rather than discarding it. No assumption that every
  component of a mapping object is contractible or Kan is made.
- Empty target quasicategories and larger target universes are allowed. The marks are
  exactly the source's arrows/image edges, and the full-subcomplex formula tests every
  vertex in every degree, not only objects or cores.

Searches for an existing statement (all run through the prescribed `msearch.py` wrapper):

- LeanFinder query: `A simplicial category whose interval tensor projections are weak
  equivalences has equivalent ordinary and enriched infinity localizations`.
  Eight hits: ordinary cofibrant-object localizations, left/right homotopy factoring,
  the truncated nerve adjunction, `QCat.catEnrichedOrdinaryCategory`, and the enrichment
  on simplicial objects. Their displayed types contain no enriched interval criterion
  or full infinity-localization comparison.
- Loogle query: `"SimplicialNerve"`. One hit, `CategoryTheory.SimplicialNerve`, the
  definition only. Its full source was read, including its future-work paragraph;
  it contains no interval-localization theorem.
- Mathlib grep query: `interval.*localization|SimplicialNerve` in `AlgebraicTopology`.
  Five hits, all the coherent-nerve file's documentation or definition, no match.
- LeanSearch query: `Homotopy coherent nerve interval tensors infinity localization`.
  Eight hits: monoidal ordinary-localization constructions, truncated nerve/homotopy
  adjunctions, and `Nerve.quasicategory`. None has the required statement.
- Direct `rg` in the source `WeilConjectures` and side project's `lean/Sheaf` for
  `lem-coef-simplicial-interval-localization|interval.*localization`: no matching
  declaration. `dag/lean_names_upstream.json` has no occurrence of this item id.
- Direct `rg` in Mathlib, source `WeilConjectures`, and `lean/Sheaf` for all seven chosen
  declaration names found no collisions. The nearby recorded coherent-nerve and
  hammock-localization source interfaces were read and reused as described above.

Validation: the delivered file compiled separately through `scompile.py`, in both
its sandbox and library-path checks, with no diagnostics. The final theorem is the
only postponed proof. The report and node record are prepared for the required
`deliver2.py --no-push` preflight; no push or second reading is performed by this worker.
No STATEMENT-DISPUTED issue, source correction, new node, or dependency repair is needed.

## Second reading by ND

I independently read the original node, its sandbox copy, the entire delivered module,
both statement dependencies and their recorded declarations, and the Mathlib definitions
below them. I read HA Proposition the project server on printed p. 110, Notation the project server,
Proposition the project server, and the proof on printed pp. 113–114 in the cited online PDF.
This item has no Stacks source. I also read the blueprint ancestor's second proof
paragraph. There is no repair note or statement correction to audit.

My object/hypothesis/conclusion checklist, matched against the Lean, is:

1. A small simplicial category and its vertex category: `A : SCat.{u}` and
   `underlying A`. PASS. The dependency's infrastructure defines these as
   `EnrichedCat SSet` and `ForgetEnrichment SSet A`. Mathlib's
   `SimplicialCategory.homEquiv'` identifies ordinary arrows with mapping vertices.
   These are not homotopy-category arrows or equivalence classes.
2. A class containing all isomorphisms and satisfying two-out-of-three:
   `W : MorphismProperty (underlying A)`, `hiso`, and the three implications in
   `hcomp`. PASS. All three implications have the right composition order; no
   saturation or additional closure is assumed.
3. An interval object for every object and its universal path: `I` and `h`.
   PASS. They require no functor structure on `I` and no other tensors.
4. Composition with that path is an isomorphism of simplicial sets, natural in
   the output object: `intervalTranspose` and `[htensor]`. PASS. The definition
   curries `(h x ⊗ₘ 𝟙 _) ≫ eComp SSet x (I x) y`, so it is exactly the specified
   composition map. Its naturality follows from enriched associativity; it is not
   an arbitrary mapping-object isomorphism. Cartesian closure permits the
   interval-first curry convention without changing the function complex.
5. The projection is the transpose of the constant identity and belongs to `W`:
   `intervalProjection` and `hp`. PASS. Following `homEquiv'`, `constantDiagrams`,
   and `inv` shows that the definition takes precisely this unique vertex. Its
   inverse is supplied by `htensor`, not an unproved existence choice.
6. The chosen object-preserving locally Kan replacement: `B`, `r`, `hobjects`,
   `hr`, `hkan`, and `hweak`. PASS. The type equality and heterogeneous object
   equalities express the common object set and identity object map, as in the
   dependency's `LocallyKanReplacement`. `IsLocallyKan` tests all mapping sets.
   `IsWeakHomotopyEquivalence` tests realization components and every positive
   based homotopy group. Neither functorial replacement nor local Kan fibrancy
   of `A` is assumed.
7. The coherent nerve of the selected replacement is the node's `D`:
   `nerveFunctor.obj B`. PASS. This is exactly the dependency's
   `SimplicialNerve (underlying B)`. The dependency's
   `CoherentNerveComparisonStatement.locally_kan_quasicategory` gives its
   quasicategory property from `hkan`; no additional hypothesis is needed.
8. The canonical ordinary-to-coherent nerve map: the existential `θ` and
   `IsIntervalNerveMap r θ`. PASS. Reading Mathlib's thickening and nerve definitions
   verifies that the object formula is `r` on the input string and the entire map
   on each thickened hom is constant at `r` of its composite arrow. A path `p`
   supplies comparability of its endpoints. These equations determine every
   enriched simplex; for incomparable endpoints the source mapping object is
   empty and its map is unique. Thus the existential does not allow an unrelated
   comparison or merely a vertexwise approximation to the canonical map.
9. The two markings: `intervalOrdinaryMarking A W` consists of the actual
   `ComposableArrows.mk₁ f` with `W f`, and `intervalCoherentMarking W θ` consists
   exactly of their `θ` images. PASS. No extra coherent edges are marked.
10. Entire full functor subcategories on inverting functors:
    `intervalInvertingDiagrams`. PASS. The dependency's `fullSubcomplex` retains
    every simplex whose vertices satisfy its predicate. Decoding a vertex using
    `SSet.unitHomEquiv` and `Functor.natTransEquiv` gives an actual simplicial
    map, and the predicate tests each marked edge with the dependency's
    `IsEquivalenceEdge`. Noninvertible transformations are retained.
11. For every infinity category, restriction is an equivalence:
    `∀ (E : SSet.{max u w}) [SSet.Quasicategory E], ∃ restriction, ...`.
    PASS. The direction is from the coherent to the ordinary inverting diagrams.
    Its equation with the two inclusions identifies it on every simplex with
    `(MonoidalClosed.pre (SSet.uliftFunctor.{w}.map θ)).app E`.
    `IsFunctorEquivalence` means a quasi-inverse and coherent natural inverse
    equivalences. The node's equivalent localization formulation follows from
    this full functor universal property; it is not a missing independent clause.
12. No original-mapping fibrancy, model structure, or further tensor assumptions:
    PASS by inspection of every binder. Both `u` and `w` are explicitly bound.
    A common sufficiently large `u` houses source objects and mapping sets;
    arbitrary larger target sizes are handled by `max u w` and degreewise lift.
    The chosen canonical `θ` precedes the quantifier over `E`.

Edge cases: no object inhabitation, nonempty index, characteristic, field, or ring
assumption occurs. The empty simplicial category and empty target are allowed.
Empty mapping objects impose no accidental choice: the canonical-map predicate
uses actual paths. At `n = 0` it fixes the image object and identity mapping map;
all degenerate simplices are included. Discrete enrichment, the terminal category,
and a zero object when present are covered. Both the all-arrow marking and the
isomorphism-only marking are admitted, with the stated projection condition still
required. Empty schemes and characteristic restrictions are not notions in this item.

I independently searched using different wording through `msearch.py`:

- LeanFinder: `Tensoring a simplicial category with Delta one detects the universal
  localization of the ordinary category at weak equivalences`. Eight hits, concerning
  ordinary model-category localizers or the Cat enrichment of quasicategories; none
  states this interval criterion or its full functor-category conclusion.
- Loogle: `"SimplicialNerve", "IsLocalization"`. Zero hits.
- LeanSearch: `An interval object with weak equivalence projection compares the infinity
  localization of a simplicial category and its underlying category`. Eight hits,
  including `Cylinder.weakEquivalence_π` and ordinary localization constructions;
  their displayed signatures do not assert this comparison.
- Direct `rg` across Mathlib, upstream `WeilConjectures`, side `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `interval.*localiz|localiz.*interval` and the
  distinctive helper/theorem names found only unrelated Tor/localization prose.
  I opened Mathlib's `SimplicialNerve` and `SimplicialCategory.Basic`; these supply
  the notions used here and no matching interval-localization statement.

No H3/H4 mismatch was found, and no Lean or node edit is needed. There are no new
nodes or dependency modules. The six helpers are concrete constructions or predicates
belonging to the item's own notation; none privately redefines a recorded dependency.
The sole postponed theorem is `simplicial_interval_localization`; no theorem is proved.
All declaration docstrings name the source and blueprint, and the theorem docstring
follows all seven DAG proof steps, including their dependencies. The two already-stated
proof dependencies are imported non-publicly. The unstated proof-only dependency
`lem-coef-enriched-marked-realization` is named in the proof plan and needs no new
statement interface to type this theorem.

Validation: `scompile.py ND lem-coef-simplicial-interval-localization` compiled the
delivered module cleanly in both sandbox and library-path checks (1.4 s and 1.6 s).
The node's `lean.statement` is verbatim equal to the source signature; all Lean lines
have at most 100 characters. The only node field changed from the shared base is
`lean`. This second reading changes only this report, preserving the worker report.
