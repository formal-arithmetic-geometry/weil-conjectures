## Worker report

The module `Sheaf.CategoryTheory.InfinityCosliceColimitFormula` states
`SSet.Enhanced.infinity_coslice_colimit_formula`. Its only theorem has proof `sorry`.
The remaining declarations give concrete helper constructions for precisely this node's
coherent coslice and pushout-cocone formula. No definition contains `sorry`, no object
is chosen from an unproved existence theorem, and no independent notion is introduced.
There is no statement correction or disputed statement.

Sources read: [HTT](https://people.math.harvard.edu/~lurie/papers/HTT.pdf),
Proposition the project server and Remark the project server (printed p. 296), the coslice mapping-space
identification in Lemma the project server and the constant-diagram case of Proposition the project server;
[Kerodon Proposition the project server, Tag 02PH](https://kerodon.net/tag/02PH).
The reference is Kerodon, not Stacks. The theorem docstring reproduces the node's eight
proof steps, including the empty-index case, compact cubes, compact finite support and
the moving-basepoint argument. No proof is supplied in this stage.

### Hypotheses and clauses

* Universes and size: `universe u v`; `C : SSet.{max (u + 1) v}` uses a containing
  universe above the small universe `u`. `Presentability.IsSmall.{u, max (u + 1) v} K`
  is the published smallness predicate, rather than requiring the ambient model to
  lie literally in the small universe. No local-smallness condition is imposed on C.
* C is a quasicategory: `[Quasicategory C]`. All small colimits:
  `hC : Presentability.HasSmallColimits.{u, max (u + 1) v} C`.
* X is any object: `X : C _⦋0⦌`. K is any small simplicial set: the first conjunct
  quantifies over `K` and `IsSmall K`, with neither `Quasicategory K` nor a vertex or
  nonemptiness assumption.
* The specified coslice is `coherentCoslice C X`, an abbreviation for the recorded
  `fiber (evaluation Δ[1] C vertex0) X`. By the definition of `fiber`, this is exactly
  `{X} ×_C Fun(Δ[1],C)`. `coherentCosliceInclusion` is `pullback.snd`.
  Thus `q : K ⟶ coherentCoslice C X` is the actual coherent diagram of arrows with
  common source, and `q ≫ coherentCosliceInclusion C X` is alpha in uncurried form.
  Source evaluation is constant at X in every simplicial degree by the pullback
  equation; target evaluation is the node's Y. This is the full coherent category,
  not an ordinary `Under` category or a homotopy category.
* A and B and the induced b are encoded together by a cocone `t` on this arrow diagram.
  Its two images under source and target evaluation must be `IsColimiting`, so their
  apices are A = colim constant X and B = colim Y. The arrow apex `t.1.1` is b : A → B.
  Its entire coherent cocone ties b to alpha; b is not an arbitrary arrow. The first
  existential asserts that these compatible colimit cocones exist. The following
  universal clause applies to every such choice, using `∀ i : Fin 2` for its two
  endpoint colimits.
* A pushout construction is `CoslicePushoutConstruction X q t τ`, with
  `τ : (coconeCategory q) _⦋0⦌`. Its `comparison` is an edge in the cocone category
  of the original arrow diagram. `source` fixes its source as t; `target` fixes its
  target as the actual `Spaces.mappedCocone` of τ under the fiber inclusion.
  Consequently the source projection is a morphism of coherent constant-X cocones
  from the A-colimit cocone to the identity constant cocone with apex X. Its apex
  is exactly the induced a : A → X. The apex of `comparison` is the square
  b : A → B to u : X → P, so its other edge is v : B → P. All the homotopies relating
  q, the endpoint colimit cocones and this square are retained in that one edge of
  the coherent cocone category. In particular, a choice of a different homotopy
  for a bare square cannot masquerade as the given construction.
* `squareCocone` uses the recorded `SuspensionComparison.SquareCocone` for that very
  apex square, uncurried from `comparison.1.1`. The recorded walking span
  `SuspensionComparison.puncture false` omits the terminal square vertex; it has
  vertices A, X, B and edges a and b. The recorded `sweep false` contracts it to
  the terminal vertex by pointwise maximum in both interval coordinates.
  `SquareCocone` fixes both apex and full coherent cocone. The field `pushout`
  requires `IsColimiting` for this exact span cocone.
  Thus P is X amalgamated over A with B, with the specified square homotopy.
* Availability of the pushout construction is the existential
  `∃ τ, Nonempty (CoslicePushoutConstruction X q t τ)`. Its universal property is
  `∀ τ, CoslicePushoutConstruction X q t τ → IsColimiting q τ`.
  This states the formula for every coherent pushout construction, with the induced
  cocone specified by its comparison data, and asserts that the construction exists.
  The extra-looking existence clauses merely spell out the colimits and induced
  cocone that the node introduces with “put” and “with the coherent cocone induced”.
* For weakly contractible K, the second conjunct uses the recorded `IsContractible K`.
  It quantifies over every colimit t of constant X and every identity constant
  cocone s (its apex is X and its arrow is the constant identity edge in Fun(K,C)).
  For every comparison edge e : t → s it asserts `IsEquivalenceEdge C e.1.1`.
  Here `e.1.1` is precisely a : A → X; this is the specified map, not existence of
  an unspecified equivalence between A and X. The endpoint and identity equations
  on s and e retain the identity-cocone characterization of a.
* Infinite regular kappa: `(κ : Cardinal.{u}), κ.IsRegular`; Mathlib's regularity
  includes infinitude. Every small kappa-filtered quasicategory: the next conjunct
  binds `[Quasicategory I]`, `IsSmall I`, and `IsKappaFiltered κ I`, and concludes
  `IsContractible I`. There is no countability, uncountability or extra inhabitation
  condition. The recorded filteredness definition tests the empty diagram too.
* Preservation by the point-selecting functor is
  `Presentability.PreservesColimitsIn (SSet.const (X := Δ[0]) X)`.
  Its class predicate requires that I be a small kappa-filtered quasicategory.
  The recorded preservation definition maps the entire cocone and tests every
  colimiting input cocone, so this covers arbitrary colimit choices in the point.
* Terminal accessibility is `∃ hT : Quasicategory Δ[0], @IsAccessible.{u,v} Δ[0] hT`.
  This supplies the terminal quasicategory structure rather than adding it as an
  assumption or declaring a separate untracked theorem/instance. Accessibility is
  the full published definition with locally small mapping spaces, existence of
  filtered colimits, compactness via the coherent corepresented functor into spaces,
  and essentially small full generation.

### Dependency declarations

Read the statements and full Lean records of the two original statement dependencies,
and read the following definitions with their docstrings:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `evaluation`, `constantDiagrams`,
  `diagramVertex`, `fullSubcomplex`, `IsEquivalenceEdge`, `IsContractible`,
  `commaSubcomplex`, `coconeCategory`, and `IsColimiting`. The docstrings define the
  endpoint-pullback model, right-pinched mapping spaces and realization-based weak
  equivalence. These definitions are reused directly.
* `Sheaf.CategoryTheory.PresentableInfinityCategory`: `IsSmall`, `IsKappaFiltered`,
  `HasSmallColimits`, `IsAccessible`, `IsKappaAccessible`, `IsLocallySmall`,
  `IsKappaCompact`, and `PreservesColimitsIn`. Initially the local DAG snapshot had no
  Lean record for this dependency; the prescribed `scompile.py --source` lookup
  found the published module, and its record has since appeared in the refreshed
  shared snapshot. No replacement dependency definition was needed.
* `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`: `mappedCoconeData`,
  `mappedCoconeData_mem`, `mappedCocone`, `PreservesColimit`, and `corepresented`.
  In particular the cocone image is the real postcomposition construction, including
  the natural transformation, rather than an arbitrary supplied image cocone.
* `Sheaf.CategoryTheory.InfinityFibrations`: `fiber`, the actual degreewise pullback.
  Its already landed node `def-coef-infinity-fibrations` is added to `stmt_deps`
  solely to cite the recorded construction used for the node's specified coslice.
  This is the authorized addition of a landed declaration, not a new definition node.
* `Sheaf.CategoryTheory.SuspensionSquareComparison`: `square`, `puncture`, `sweep`,
  `boundary`, `conePath` and `SquareCocone`. A broader duplicate search found these
  already published constructions, so the equivalent draft helpers were removed.
  The existing node `lem-coef-suspension-square-comparison` is added to `stmt_deps`
  for these unrestricted square helpers; its pointed-category theorem is not used.
  Read that node's statement and complete Lean record and the complete module.
  A read-only traversal of statement and proof dependencies found no path from
  that node to this item (418 nodes reached), so this import introduces no cycle.
* Mathlib: `SSet`, `Quasicategory`, `stdSimplex`, `stdSimplex.objMk`, `ihom`,
  `MonoidalClosed.curry`/`uncurry`, degreewise simplicial products and pullbacks,
  and `Cardinal.IsRegular`.

All currently stated proof dependencies are imported without `public`: enhanced
functor/cone calculus; realization compact finite support; realization CW subcomplex;
simplicial groupoid localization; homotopy-group basepoint change; Kan homotopy-pullback
invariance; realization cylinder; and the Mathlib compact standard-simplex module.
`lem-coef-infinity-yoneda-presheaf-limits` has no published Lean record at this reading,
so its future proof-only import is omitted. It is not needed to type the statement.

### Edge cases

* K empty: the first conjunct accepts it. A and B are initial; a and b have initial
  source, the pushout is X, and τ has apex equivalent to id_X, the initial coslice
  object. No choice of a vertex of K enters any helper.
* K a point: A is X, a is the canonical equivalence and the pushout is B. The formula
  reduces to the value of the one-object diagram.
* K two discrete points: A is X coproduct X and P is the pushout along the two source
  maps; the formula does not incorrectly assert that the underlying coproduct of the
  two targets itself receives a common-source coslice cocone.
* X initial: the coslice reduces to C up to equivalence, A is initial for every K,
  and P reduces to B, including the empty case.
* Filtered I empty is excluded by the actual empty-diagram clause of
  `IsKappaFiltered`; no redundant `Nonempty` hypothesis is introduced.
* K weakly contractible need not be a quasicategory. The constant-comparison clause
  makes no such restriction. K empty does not satisfy `IsContractible`.
* Kappa = aleph zero is included by `IsRegular`, and all proofs of weak contractibility
  in the docstring use finite support only. Higher regular cardinals remain included.
* A quasicategory C need not be locally small; all mapping-space tests are taken in
  the ambient containing universe. No universe equality is imposed.
* The point is not assumed to have a preinstalled quasicategory instance: its
  structure and accessibility are concluded together. The main assertion has no
  hollow point-quasicategory hypothesis.

### Searches

The prescribed wrapper `msearch.py Q38 lem-coef-infinity-coslice-colimit-formula` was used:

1. `leanfinder`, query “colimits in coherent coslice quasicategories are pushouts and
   filtered quasicategories are weakly contractible”: eight hits, led by
   `SSet.hasColimits`, `SSet.Truncated.hasColimits`,
   `CategoryTheory.Limits.isColimitOfIsPushoutOfIsConnected` and the ordinary nerve
   quasicategory instance. None states this coherent coslice formula.
2. `loogle`, query `"Under", "colimit"`: twelve hits, including
   `Under.isColimitLiftCocone` and `Under.hasColimit_of_hasColimit_liftFromUnder`.
   Read their signatures/docstrings in Mathlib `Comma/Over/Basic.lean` and
   `WithTerminal/Cone.lean`. They concern ordinary categories and Hom sets;
   the former additionally needs a nonempty index and is not the empty-index
   coherent pushout formula. No exact match.
3. `grep`, query `coslice|Quasicategory.*[Ff]ilter|[Pp]resentable.*[Ii]nfinity`,
   subdirectory `AlgebraicTopology`: zero hits.
4. `leanfinder`, query “presentable accessible infinity category kappa filtered
   coherent diagrams quasicategory”: ordinary presentability/accessibility results,
   no coherent replacement. The published dependency found by the live-source
   lookup is used instead of duplicating it.
5. `rg` over upstream `WeilConjectures` and project `lean/Sheaf/CategoryTheory` for
   coslice, Coslice, kappaFiltered, IsAccessible and IsPresentable found ordinary
   presentability and the project's join-slice/source-fiber work. Read
   `ArrowSourceFibers.lean`: it concerns source fibers of pushout-stable arrow
   classes and does not state this colimit formula. The existing `fiber` is reused.
   `RelativeInfinityCone.lean` and `InfinityColimitGluing.lean` were also read:
   their universal and gluing interfaces are related, but neither states this node.
6. Upstream literal node-id search with `grep -rn` returned no match. Searches of
   `dag/lean_names_upstream.json`, upstream Lean and `lean/Sheaf` for the new helper
   names and theorem name returned no duplicate. A broader search for all square
   and pushout definitions found `SuspensionSquareComparison.SquareCocone`, which
   is now reused. `PointedModelStability.IsPushoutSquare` was also read; it uses
   another nerve square model and is not needed because the exact product-square
   model is already supplied by `SuspensionSquareComparison`. No square, maximum
   map, walking-span predicate or square-cocone predicate is redefined here.

### Validation

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q38
lem-coef-infinity-coslice-colimit-formula <module>` passed both the sandbox and
library-path server compilations of the final version, in 2.2 and 2.4 seconds, with no errors or
warnings. All variables and universe levels are explicitly bound; `autoImplicit`
is false. Every line is at most 100 characters. Only the theorem's proof is `sorry`.
The final worker gate is `deliver2.py Q38 lem-coef-infinity-coslice-colimit-formula
--no-push`. The second-reading section is intentionally left for the independent
reader; the worker does not write that section or push the delivery.

## Second reading by Q38

Independent reader, 2026-10-17. I read the natural statement and all eight proof
steps, the delivered Lean module, and the signatures and definitions of all four
statement dependencies. There is no repair note for this item. The item has no
`statement_change`; its natural statement and proof are unchanged. No new nodes
or dependency modules are delivered.

I checked the actual source places in [HTT](https://people.math.harvard.edu/~lurie/papers/HTT.pdf):
Proposition the project server and Remark the project server (printed p. 296), Proposition the project server
(printed pp. 267--268), and Lemmas the project server--13 (printed pp. 489--490).
The first is a gluing/pushout theorem, not literally this coslice formula; the
node correctly labels its formula as an agent construction from those results.
Remark the project server requires the maps induced by the chosen colimit cocones, up to a
contractible space of choices. Lemma the project server requires only an infinity category
and common-source arrows; it adds no presentability or local-smallness hypothesis.
Proposition the project server over a point applies to the identity constant cocone for a
weakly contractible simplicial set. I also read the statement and proof of
[Kerodon 02PH](https://kerodon.net/tag/02PH): every filtered infinity category is
weakly contractible, proved using finite simplicial subsets and contractions.
Only finite diagrams are needed, so every infinite regular kappa is covered.
There is no Stacks source or ambient ring/scheme hypothesis to add here.

My object/hypothesis/conclusion checklist, matched to the Lean:

1. **Size convention and ambient category.** The containing simplicial universe is
   `max (u + 1) v`, the small universe is `u`, and `C` has `[Quasicategory C]` and
   `hC : Presentability.HasSmallColimits.{u, max (u + 1) v} C`. I opened the
   definition: it quantifies over every small simplicial indexing set and every
   diagram, with no quasicategory condition on the index. This is exactly the
   node's convention from `def-coef-presentable-infinity-category`. No local
   smallness, accessibility, pointedness or extra colimits of C are assumed. Pass.
2. **K, X and the specified coherent coslice.** The first conjunct binds any `K`
   satisfying `Presentability.IsSmall`, then any vertex `X`, then
   `q : K ⟶ coherentCoslice C X`. The abbreviation unfolds to the recorded
   `fiber` of source evaluation. I read `InfinityFibrations.fiber`: it is the
   actual pullback of the constant point and that evaluation map.
   `coherentCosliceInclusion` is its `pullback.snd`. Thus all simplices, rather
   than just objects and homotopy classes, have source constantly X. Pass.
3. **Y, alpha and their endpoint colimits A and B.** The arrow diagram is
   `q ≫ coherentCosliceInclusion C X`; target evaluation gives Y and source
   evaluation gives the constant diagram on X. A cocone `t` in this arrow
   diagram's `coconeCategory`, whose two `Spaces.mappedCocone` images are
   `IsColimiting`, records A, B and the induced b together. The initial
   existential supplies such compatible endpoint colimits, and the universal
   clause covers every such t. The `Fin 2` endpoint test has exactly the two
   vertices of the interval. I read `mappedCoconeData` and `mappedCocone`: they
   postcompose the actual apex and the full coherent transformation. Pass.
4. **Canonical a and the induced coslice cocone.**
   `CoslicePushoutConstruction.comparison` is an edge in the cocone category of
   that same arrow diagram. Its source is t and its target is the actual image
   of tau under the fiber inclusion. The source-evaluation projection of this
   target is the identity constant-X cocone, because tau lives in the strict
   source fiber in every degree. Its comparison therefore induces a from A to X.
   The target-evaluation projection retains the induced cocone from Y to P.
   These endpoint conditions prevent substituting unrelated arrows or square
   homotopies for the canonical comparison. Pass.
5. **P is the specified pushout, and its arrow is colimiting.** Uncurrying the
   apex `comparison.1.1` gives the square with corners A at (0,0), B at (1,0),
   X at (0,1), P at (1,1). I read `SuspensionComparison.puncture`, `sweep`,
   `boundary`, `conePath`, and `SquareCocone`: `puncture false` is the walking
   span A to B and X; the square fixes both the resulting cocone apex and its
   complete coherent path. The `pushout` field asserts `IsColimiting` for that
   exact cocone. The theorem asserts existence of tau with this construction
   and `IsColimiting q tau` for every such construction. This expresses both
   the existence implicit in the node's “put” and the asserted formula for its
   induced coherent cocone. No arbitrary map or mere existence choice is used
   to define P. Pass.
6. **Weakly contractible K and the specific a.** The second conjunct binds small
   K with `IsContractible K`, every colimit t of the constant diagram, and s
   whose apex is X and whose transformation is the degenerate identity at that
   diagram. For every comparison edge e from t to s it concludes
   `IsEquivalenceEdge C e.1.1`. I checked that `.1.1` is the apex edge, hence
   precisely a, and that `constantDiagrams` gives the identity edge used in the
   equation for s. The conclusion concerns the specified comparison, rather
   than an unspecified equivalence between its endpoints. Pass.
7. **Every infinite regular kappa and every small filtered infinity category.**
   The third conjunct binds `κ : Cardinal.{u}` with `κ.IsRegular`, followed by
   arbitrary small `I` with `[Quasicategory I]` and `IsKappaFiltered κ I`, and
   concludes `IsContractible I`. The dependency's definition tests the empty
   diagram as well. `IsContractible` is the recorded realization weak homotopy
   equivalence to the point, including components and every positive based
   homotopy group. Pass.
8. **Preservation by the point-selecting functor.** For every X the next clause
   uses `Presentability.PreservesColimitsIn (SSet.const (X := Δ[0]) X)`.
   Its predicate specifies exactly small kappa-filtered quasicategories.
   I opened `PreservesColimitsIn`: it tests every actual colimiting cocone and
   its actual `mappedCocone`, not just existence of an output colimit. Pass.
9. **Accessibility of the terminal quasicategory.** The last conjunct supplies
   `hT : Quasicategory Δ[0]` and the recorded
   `@Presentability.IsAccessible.{u,v} Δ[0] hT`. I read its dependencies through
   `IsKappaAccessible`, `IsKappaCompact`, and the space-valued corepresented
   colimit test. It is the full accessibility assertion, including local
   smallness, filtered colimits, compact objects and essentially small full
   generation. The quasicategory structure is concluded, not assumed. Pass.

Edge cases checked independently: K empty is admitted and gives initial A and B,
then P equivalent to X and the initial coslice arrow id_X. A singleton K recovers
its sole arrow. For two discrete points the source colimit is X coproduct X, so
this statement does not mistakenly use the coproduct of targets alone. Initial
X reduces the construction to the colimit in C. Weakly contractible K is not
required to be a quasicategory; empty K does not satisfy weak contractibility.
Empty I fails the empty-diagram requirement of filteredness. Mathlib's
`Cardinal.IsRegular` includes infinitude, and `isRegular_aleph0` confirms the
aleph-zero case is present. The node has no numerical degree, ring
characteristic or scheme case to specialize. The zero-dimensional cube case
appears explicitly in proof step 5. The ambient universe admits the mapping
spaces without a locally-small assumption or an extra universe equality.

Independent duplicate searches (recorded by the prescribed msearch wrapper):

- LeanFinder query `quasicategory undercategory colimit pushout constant source`:
  eight hits, principally simplicial horn/subcomplex pushouts and ordinary
  `Under.pushout_obj`/`Under.pushout_map`; none states this coherent theorem.
- Loogle query `"Under", "colimit"`: twelve hits. I opened
  `CategoryTheory.Under.isColimitLiftCocone` in Mathlib's `Comma/Over/Basic.lean`:
  it uses ordinary categories and `[Nonempty J]`, and cannot replace the
  empty-index coherent formula. Other hits concern ordinary Under colimits.
- Wrapper grep query `sourceFiber|coslice|underCategory`: three ordinary-comma
  documentation hits, no exact match.
- Independent `rg` on upstream WeilConjectures, Mathlib's simplicial-set/comma
  sources, and the project's CategoryTheory modules used `coslice`,
  `undercategor`, `source.fiber`, `constant.*contractib`, and
  `filtered.*contractib`. I opened `ArrowSourceFibers` (a pushout-stable arrow
  class theorem), `FilteredNerveWeakContractibility` (ordinary category nerves
  only), and the `firstVertexCoslice`/`joinCoslice` declarations (join models,
  not the specified strict arrow fiber). These are related but not duplicates.
  The actual fiber and square-cocone notions are reused from their recorded
  modules. Searching all upstream names and source/project Lean for the new
  theorem and helper names found no collision.

The docstring has all eight proof steps, including the induced-map mapping-space
comparison, empty case, compact finite support and moving-basepoint argument.
Every declaration has a source and the item's blueprint tag. The sole `sorry`
is the whole proof of `infinity_coslice_colimit_formula`; helper definitions
contain real data. No file-local notation, private copy, extra instance, or
unbound variable/universe is present. `lean.statement` is verbatim equal to the
file's signature; all lines are at most 100 characters. The only delivered node
changes from the shared snapshot are `lean` and the two already-landed helper
nodes added to `stmt_deps`.

**Mismatches and changes:** none found; I retained the Lean module and node record
unchanged and appended this independent reading. I ran the required scompile.py
on the sole delivered module: sandbox compilation passed in 2.5 seconds and
library-path compilation passed in 2.7 seconds, with no errors or warnings.
