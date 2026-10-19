## Worker report

The statement is `HomotopicalAlgebra.BrownReedy.brown_reedy_fibrant_replacement`
in `Sheaf.CategoryTheory.BrownReedyFibrantReplacement`. Its only postponed proof
is the named theorem for the item. Its docstring contains all sixteen DAG proof
steps, including the general fibrant-subcategory localization input in step 15.
The item's mathematical statement is unchanged. Its stmt_deps gains the new
Brown/Reedy definition node and the already landed coherent-localization interface.

The definitions are in `Sheaf.CategoryTheory.BrownReedyDiagrams`, owned by the
new node `def-coef-brown-reedy-diagrams`. Every definition has real data; there
is no selection of a replacement or a localization from the theorem's `sorry`.
Existence of limits is expressed using limiting cones, and relative matching
maps are characterized by the actual pullback square and both projections.
This is the ordinary universal-property presentation of the node's constructions.

Hypotheses and definitions, clause by clause:

- Ordinary category C: `(C : Type u) [Category.{v} C]`; the terminal object and
  classes are `(one : C) (W F : MorphismProperty C)`.
- All Brown assumptions are `hBrown : BrownAxioms one W F`.
  Its first conjunct is `Nonempty (IsTerminal one)`. The next conjunct says
  every `IsIso f` satisfies both `W f` and `F f`.
- Its third conjunct contains composition closure for W, both cancellation
  implications of two-out-of-three, and composition closure for F, for all
  composable arrows. All arrows to `one` are in F in its fourth conjunct.
- Its fifth conjunct gives an actual `IsPullback a b p f` and `F b` for every
  F-map p and arbitrary f. Different choices of pullback differ by an
  isomorphism, and composition/isomorphism closure already in BrownAxioms
  transports F to every pullback. Thus this is exactly existence and base-change
  closure, without assuming other pullbacks exist.
- Its sixth conjunct is preservation of `F ∩ W` in every such pullback square.
  Its last conjunct is `∃ Z w p, W w ∧ F p ∧ w ≫ p = f` for every f.
  No functorial factorization, model structure, completeness, or retract axiom
  occurs among the assumptions.
- The finite inverse shape is `(K : Type w) [Category.{z} K] [Finite K]`
  and `[∀ i j : K, Finite (i ⟶ j)]`, with `degree : K → ℕ` and
  `hdegree : FiniteReedy.IsInverse degree`. That existing predicate says an
  arrow is a transported identity or strictly decreases degree, allowing all
  identities and excluding all other degree-preserving arrows.
- `boundaryProjection k` uses `(coefLatchingIndex (op k))ᵒᵖ`. An object of the
  slice over op(k) is an opposite arrow op(j) → op(k), hence k → j.
  Reversing its commuting triangles gives exactly the coslice triangles under k.
  The right objects are not identified: two parallel arrows remain two objects.
  The predicate deleting identities is exactly the existing coefLatchingIndex
  predicate, including transport along equality of objects.
- The projection is `(coefLatchingProjection (op k)).leftOp`, hence codomain
  j in K. `boundaryCone X k` uses the actual arrows `X.map a.unop.obj.hom.unop`.
- `IsReedyFibrant F X` says, for every k, `∃ c hc, F (hc.lift (boundaryCone X k))`
  where c is a cone over the boundary restriction and hc is its `IsLimit`.
  In particular existence of every matching object is asserted, not assumed.
- `RelativeMatching P f k` specifies both limiting cones, the induced matching
  map by `hd.lift ((Cone.postcompose ...).obj c)`, a pullback of that map and
  Y's matching arrow, and the arrow r with `r ≫ a` equal to X's matching arrow
  and `r ≫ b = f.app k`, together with `P r`. These equations uniquely
  determine r. Isomorphism closure makes this existential presentation
  independent of all choices of limiting cones and pullback representatives.
- `ReedyFibrations F f` includes fibrancy of X,Y and all relative tests in F.
  `ReedyDiagrams K F` is Mathlib's `ObjectProperty.FullSubcategory` on that
  predicate. `reedyWeakEquivalences` is `W.functorCategory K` on underlying
  transformations; `reedyFibrations` is the relative matching class there.
- `FiniteReedy.IsLocalization` is used as recorded in the landed definition
  node: it quantifies over whole internal functor simplicial sets and their full
  inverting subcomplexes. It retains every transformation and higher simplex.
  `SSet.Enhanced.IsFunctorEquivalence` and `AreNaturallyEquivalent` are the
  exact recorded enhanced notions, with coherent inverse witnesses.
- Universes u,v,w,z,t are bound explicitly and independent. Localizations lie
  in `SSet.{max u v w z t}`; the boundary shape's object universe is max w z.
  RestrictionPreserves has additional independent index universes, so boundaries
  and full subcategories can both be used without forcing an equality of sizes.

The conclusion is a conjunction in the following order:

1. There exists a proof `ht` of fibrancy of the actual constant diagram at one.
   `BrownAxioms ⟨(Functor.const K).obj one, ht⟩` is asserted for exactly the
   full Reedy category with the two classes just defined. This includes its
   terminal-object, all-fibrant, pullback, weak-equivalence and factorization
   axioms, and identifies its terminal object as the specified constant diagram.
2. Every pullback square in that Reedy category along a Reedy fibration is an
   `IsPullback` after every evaluation k. Existence is already supplied by its
   Brown axioms, so this says pullbacks along those arrows are computed objectwise.
3. Every arbitrary strict X has `∃ Y u, W.functorCategory K u` with
   `Y : ReedyDiagrams K F` and `u : X ⟶ Y.obj`: the required direction X → RX.
4. There exist coherent localizations q of all strict diagrams and r of Reedy
   diagrams, and an equivalence e with
   `AreNaturallyEquivalent (r ≫ e) (inclusionNerve K F ≫ q)`.
   `inclusionNerve` is the actual degreewise nerve of the full-subcategory inclusion,
   mapping a simplex s to `s.down ⋙ ObjectProperty.ι ...`. The triangle explicitly
   says inclusion induces this equivalence, not merely that unrelated equivalences
   of the two objects exist.
5. Every Reedy fibrant X has `Nonempty (LimitCone X)`: its ordinary limit exists.
6. For every Reedy fibration f and every pair of ordinary limiting cones c,d,
   `F (hd.lift ((Cone.postcompose f).obj c))` and, if f is componentwise W,
   `W` of that same canonical limit map. Together they give precisely the
   fibration and trivial-fibration assertions for limits. The unused witness hc
   is necessary to restrict the source cone to a limiting cone.
7. Every Reedy fibration is componentwise F, and componentwise W is equivalent
   to `∀ k, RelativeMatching (F ⊓ W) f k`. This is the asserted criterion that
   each relative matching map be a trivial fibration.
8. For every object predicate P closed under targets of all arrows, restriction
   along `ObjectProperty.ι P` satisfies `RestrictionPreserves W F`.
9. Restriction along every `boundaryProjection k` satisfies the same predicate.
   That predicate includes preservation of fibrant objects, of Reedy fibrations,
   and of componentwise W among those fibrations, hence of trivial ones.
10. If K is empty, both the arbitrary diagram category and the Reedy category
    are equivalent to `Discrete PUnit`. Every limiting cone then has apex
    isomorphic to one. This is the ordinary meaning of the terminal diagram
    category and its limit one, independent of chosen universal representatives.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsEquivalenceEdge`, `IsFunctorEquivalence`, and
  `AreNaturallyEquivalent`, through the recorded full coherent definitions.
- `Sheaf.CategoryTheory.FiniteReedyLocalization`:
  `HomotopicalAlgebra.FiniteReedy.largeNerve`, `Inverts`, `localDiagrams`,
  `IsLocalization`, and `IsInverse`. Only definitions are used, not its
  model-category/finite-Reedy theorem. The coherent interface has its own
  landed DAG definition node, now added to the item's stmt_deps.
- `Sheaf.CategoryTheory.DirectWeakFactorization`:
  `CategoryTheory.coefLatchingIndex`, `coefLatchingProjection`, read with their
  full signatures/docstrings. These helpers are general in both indexing
  universes and need no completeness or WFS assumptions. The theorem in that
  module has stronger hypotheses; it is not applied here.
- Mathlib `Cone`, `IsLimit`, `LimitCone`, `Cone.postcompose`, `IsPullback`,
  `ObjectProperty.FullSubcategory`, `MorphismProperty.functorCategory`, and
  `Functor.whiskerLeft` are reused directly.
- The proof dependency `lem-coef-fibrant-subcategory-localization` currently has
  no recorded Lean module. It is a future proof input, not a missing object
  used in the signature; accordingly there is no module to import. Its use
  and hypotheses are retained explicitly in proof-docstring step 15.

Edge cases checked before writing and when reviewing the type:

- Empty K: all Reedy matching conditions are vacuous, all transformations have
  the empty component family, and the limit clause uses one. The explicit last
  conjunct covers both diagram categories and any limiting apex.
- Singleton/discrete K: every boundary is empty; the matching arrow is the
  terminal arrow and its relative map is the component map up to isomorphism.
  Thus the definitions reduce to ordinary fibrancy and component fibrations.
- One arrow: the source matching object is the target value; a relative
  matching map is exactly the usual relative pullback arrow.
- Parallel arrows: boundary objects are arrows, not their codomains, giving
  distinct constraints. Diamonds retain every triangle and compatibility.
- No nonidentity endomorphisms or cycles can occur under IsInverse; ordinary
  identities are retained using equality transport, without assuming a skeletal
  category. No nonemptiness, decidable equality, or chosen object is required.
- All maps isomorphisms, W all maps, and F all maps: the predicates remain their
  intended predicates; none replaces a hypothesis by a tautology or an arbitrary
  unconstrained comparison map.

Searches for an existing statement/notion:

- msearch leanfinder: “Finite inverse diagrams in a Brown category admit Reedy
  fibrant replacement and equivalent coherent localizations”: model-category
  fibrancy and ordinary localized equivalences, no exact Brown/Reedy theorem.
- msearch loogle: `MorphismProperty.functorCategory`: service reported unknown
  identifier; its actual declaration was read directly in Mathlib Basic.lean.
- msearch grep: `Reedy|relativeMatching`, AlgebraicTopology: Reedy/Basic only
  defines index structures and lists diagram structures as future work.
- msearch leansearch: “Brown all fibrant category axioms Reedy fibrant diagrams
  using only existing matching limits and relative matching pullbacks”: model
  axioms, Brown factorization assuming ModelCategory, no matching predicate.
- msearch leanfinder: “Reedy fibrant diagrams without assuming all limits in a
  Brown category of fibrant objects”: FibrantObject and CategoryWithFibrations;
  none includes partial matching limits or relative matching tests.
- msearch grep: `BrownAxioms|IsReedyFibrant|ReedyFibrations|relativeMatching`,
  CategoryTheory: no Mathlib hits. These three new-node searches are recorded
  verbatim as search-log JSON in its mathlib_searches.
- rg of WeilConjectures/CategoryTheory for Brown/Reedy/matching and of
  WeilConjectures for the item id: no existing statement/predicate.
- rg of lean/Sheaf found the coherent interface, the general opposite latching
  boundary (reused), and ReedyModelStructure's matching definitions. The last
  require HasLimitsOfSize and HasColimitsOfSize and a wide-subcategory wrapper;
  they cannot state this Brown theorem without adding hypotheses. The new
  predicates apply universal cones directly to the existing general boundary.
- DAG rg for Brown and Reedy fibrant plus blueprint_refs search “Reedy”, “Brown”
  and “matching”: related theorem nodes and hypercovers, no separate Brown
  axiom/partial-limit Reedy definition node. blueprint_refs ancestor returns
  prop-coef-integral-exceptional-adjoint, as recorded on the new node.

Source checked: Cisinski CatLR.pdf online, paragraphs 7.4.7, 7.4.17,
Propositions 7.4.8--7.4.10 and 7.4.18--7.4.19, Theorems 7.4.20 and 7.5.18.
The original source record already notes that an archived copy is wanted.
There is no mathematical statement correction or STATEMENT-DISPUTED fault.

Validation: both delivered modules compiled separately in dependency order
through scompile.py, cleanly, with no error or warning. The only sorry is the
item's named theorem; the definitions contain none. Delivery preflight follows.

## New nodes

`def-coef-brown-reedy-diagrams` supplies the exact all-fibrant Brown predicate,
partial-limit Reedy predicates, full Reedy category with its classes, restriction
predicate, and actual lifted inclusion map used above. Source: Cisinski 7.4.6,
7.4.7, 7.4.12 and 7.4.17. Its eleven helper declarations are all listed in
lean.declarations and documented under this definition node. The three recorded
searches above found only model-category fibrancy/factorization and no general
Brown/partial-matching predicate. Existing latching boundary helpers and the
existing coherent-localization nerve interface are reused. No theorem is
postponed in this new definition node.

## Earlier second reading (a previous round; superseded)

I reread the item node, its source place, the dependency declarations, and both sandbox
modules. The source is Cisinski, *Higher Categories and Homotopical Algebra*, Definitions
7.4.6--7.4.7 and 7.4.12, Propositions 7.4.8--7.4.10 and 7.4.18--7.4.19, Theorem 7.4.20,
and Theorem 7.5.18 (ordinary-nerve specialization). The node's hypotheses and clauses
match the following Lean rendering, in order:

1. An ordinary category `(C : Type u) [Category.{v} C]`, terminal object `one`, classes
   `W F`, and all-fibrant Brown hypotheses are rendered by `BrownAxioms one W F`.
   `BrownAxioms` explicitly contains terminality, isomorphisms, two-out-of-three and
   composition, fibrancy of every map to `one`, the required pullback witnesses and
   base-change closure, and nonfunctorial `W`-then-`F` factorization. No model,
   completeness, finiteness, or functorial-choice assumption is added.
2. The finite inverse index is `(K : Type w) [Category.{z} K] [Finite K]` with finite
   homs, degree `degree : K → ℕ`, and `hdegree : FiniteReedy.IsInverse degree`. The
   latter retains equality-transport identities and strictly decreases every other
   arrow, including parallel-arrow and nonskeletal cases.
3. The deleted-identity boundary and codomain projection are `boundaryProjection k`,
   built from the existing `coefLatchingIndex`/`coefLatchingProjection`; distinct
   parallel arrows remain distinct. The matching cone is the actual cone
   `boundaryCone X k`.
4. Reedy fibrancy is exactly `IsReedyFibrant F X`, which existentially supplies a
   limiting cone for every boundary and requires its canonical lift to lie in `F`.
5. Relative matching is exactly `RelativeMatching F f k`: both matching limiting
   cones, the actual pullback square, and the uniquely characterized comparison arrow
   with both projection equations and its membership in `F` are present. Reedy
   fibrations are `ReedyFibrations F f`; the full subcategory and its classes are
   `ReedyDiagrams`, `reedyWeakEquivalences`, and `reedyFibrations`.
6. The first conclusion conjunct gives fibrancy of the specified constant diagram and
   `BrownAxioms` on the full Reedy subcategory with exactly the stated classes.
7. The second conjunct evaluates every pullback square along a Reedy fibration at every
   `k : K`, with all four maps and the original `IsPullback` square retained.
8. The third conjunct gives, for every strict diagram, the required arrow
   `X ⟶ Y.obj` to a Reedy fibrant diagram with componentwise `W`.
9. The fourth conjunct quantifies universe-lifted coherent localizations of all strict
   and Reedy diagrams, an enhanced equivalence, and the explicit natural equivalence
   induced by `inclusionNerve K F`; it is the full coherent functor-category
   localization property, not only a homotopy-category assertion.
10. The fifth conjunct gives an ordinary `LimitCone` for each Reedy fibrant diagram.
11. The sixth conjunct says that every Reedy fibration induces an `F` map on arbitrary
   chosen limiting cones and, when componentwise `W`, a `W` map as well.
12. The seventh conjunct gives componentwise `F` for every Reedy fibration and the exact
   equivalence between componentwise `W` and all relative matching maps in `F ⊓ W`.
13. The eighth and ninth conjuncts give `RestrictionPreserves` for every full
   target-closed subcategory and for every `boundaryProjection k`, including fibrant
   objects, Reedy fibrations, and componentwise weak equivalences.
14. The final conjunct includes the empty index: both diagram categories are equivalent
   to `Discrete PUnit`, and every limiting apex is isomorphic to `one`.

No mismatch was found between this list, the node's TeX statement, the Cisinski source,
and the Lean signature. In particular, no hypothesis was strengthened, no conclusion was
weakened, and no edge case was dropped. The theorem's sixteen proof-plan steps are all
present in its statement docstring, with the localization step explicitly using the
recorded future proof input.

Edge cases checked were empty `K`, singleton/discrete `K`, a one-arrow category,
parallel arrows, nontrivial equality transports, all-isomorphism `W`/`F`, and the
zero/terminal-map cases. The empty boundary is handled by the existential matching
cone and the empty index conclusion; no nonemptiness or decidable-equality assumption
is present. Object, morphism, index-object, index-morphism, and localization universes
are independently bound and the lifted nerve uses the declared enlarged universes.

The existing-declaration searches were repeated with `msearch.py` LeanFinder, Loogle,
and grep, and with `rg` over `WeilConjectures`, `lean/Sheaf`, Mathlib's Reedy files,
and the DAG. They found only Mathlib's model-category `IsFibrant` and the existing
HasLimits-based `Reedy.relativeMatching`; neither states the Brown partial-limit
notions or this theorem, so the new definition node and modules are required. The
recorded coherent-localization and latching-index declarations are used directly.

The only implementation change made during this reading was appending this report
section. Both modules compile separately through `scompile.py` with no errors or
warnings other than the item's named `sorry`; the definition module has no `sorry`.

## Second reading by Q43

I reread the item node, its source place, the dependency nodes, and the exact Lean
declarations. The source is Cisinski, *Higher Categories and Homotopical Algebra*,
Definitions 7.4.6--7.4.7 and 7.4.12, Propositions 7.4.8--7.4.10 and 7.4.18--7.4.19,
Theorem 7.4.20, and Theorem 7.5.18 (ordinary-nerve specialization). The source's
direct diagrams become the inverse category `K` with `FiniteReedy.IsInverse degree`.

The node's hypotheses and conclusion clauses render in the Lean signature as follows.

1. The ordinary category, terminal object, and classes are `(C : Type u)`,
   `[Category.{v} C]`, `one`, `W`, and `F`; `hBrown : BrownAxioms one W F` expands to
   terminality, isomorphisms in both classes, composition and two-out-of-three,
   fibrancy of every map to `one`, required pullback witnesses with fibrant base
   change, preservation of `F ∩ W`, and nonfunctorial `W`-then-`F` factorization.
2. The finite inverse indexing category is `(K : Type w) [Category.{z} K]` with
   finite objects and finite homs, a degree `K → ℕ`, and `IsInverse degree`; no
   universe equality or extra finiteness assumption is present.
3. `boundaryProjection k` is the opposite punctured slice over `op k`, transported
   by `coefLatchingProjection`; `boundaryCone X k` uses the actual outgoing arrows.
   Parallel arrows remain separate boundary objects.
4. `IsReedyFibrant F X` existentially supplies a limiting cone for every boundary
   and requires its canonical matching arrow to lie in `F`.
5. `RelativeMatching F f k` supplies both boundary limiting cones, the induced
   matching map, an actual pullback square, and the uniquely characterized arrow
   `r : X.obj k ⟶ P` with both projection equations and `F r`. `ReedyFibrations`,
   `ReedyDiagrams`, `reedyWeakEquivalences`, and `reedyFibrations` then have exactly
   the node's meanings.
6. The first conclusion conjunct gives the specified constant terminal diagram and
   `BrownAxioms` on the full Reedy subcategory; the second says every such pullback
   evaluates to an `IsPullback` at each `k`.
7. The replacement conjunct gives every strict `X` an arrow `X ⟶ Y.obj` into a
   Reedy fibrant `Y`, componentwise in `W`.
8. The localization conjunct quantifies universe-lifted localizations of all strict
   and Reedy diagrams, an enhanced equivalence, and the explicit natural equivalence
   induced by `inclusionNerve K F`.
9. The limit conjuncts give ordinary limits of Reedy fibrant diagrams, `F` and (when
   componentwise `W`) `W` for induced limit maps, componentwise `F` for Reedy
   fibrations, and the exact equivalence with all relative matching maps in `F ⊓ W`.
10. The restriction conjuncts cover target-closed full subcategories and every
    `boundaryProjection k`, including preservation of the weak-equivalence part of
    Reedy trivial fibrations. The final conjunct explicitly covers empty `K`, both
    diagram categories' equivalence with `Discrete PUnit`, and the uniqueness of a
    limiting apex up to isomorphism with `one`.

Edge cases checked were empty `K`, singleton and discrete `K`, a single nonidentity
arrow, parallel arrows, nonskeletal equality transports, empty boundaries, `n = 0`,
the terminal/zero-map cases, and classes consisting of all maps or only isomorphisms.
The independent object, morphism, index, and localization universes remain explicit.

I repeated the existing-declaration searches with `msearch.py` (LeanFinder, Loogle,
and grep), `rg` over `WeilConjectures`, `lean/Sheaf`, Mathlib Reedy/model-category
files, and the DAG. Only Mathlib's model-category fibrancy and HasLimits-based Reedy
helpers were found; no Brown partial-limit predicate or this theorem exists. The
recorded `def-coef-brown-reedy-diagrams` declarations and the existing coherent
localization interface were read directly and match their dependency nodes.

No mismatch was found between the node, Cisinski's source, the dependency interfaces,
and the Lean signatures. No statement correction, new dependency module, or code
repair was needed. I compiled both sibling modules separately with the mandated
`scompile.py`; compilation was clean, with only the item's named theorem `sorry`.
