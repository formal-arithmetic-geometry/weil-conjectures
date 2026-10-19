## Worker report

`Sheaf.CategoryTheory.LMPrismApproximation` constructs the canonical ordinary
operators and states `SSet.Enhanced.lm_prism_approximation`. Its definitions have
explicit data. No functor, prism, or forgetful map is chosen from an existence
statement, and no target operadic fibration, algebra, module, or section is a
parameter. The node copy changes `lean` and adds the newly landed canonical pointed-projection
node to `stmt_deps`.

Source checked: Lurie, Higher Algebra (2017), Construction the project server and Proposition
the project server (printed pp. 462–464), Construction the project server and Remark the project server (printed
pp. 514–515), at https://people.math.harvard.edu/~lurie/papers/HA.pdf. The displayed
block formulas agree with the node. There is no repair note for this item.

Clause-by-clause correspondence:

1. The ordinary LM category, its pure-algebra subcategory and their nerves are
   the recorded `LMOperadCategory`, `LMAlgebraCategory`, `lmBase` and
   `lmAlgebraBase`, imported from `LeftModuleOperadicEncoding`. Its `lmCutFunctor`,
   `lmCutWords`, `lmCutArrow` and nerve `lmCut` supply Cut without duplication.
2. `D = N(Deltaᵒᵖ)` is `monoidalSimplexBase.{u}`. `lmPrismObject n 0` has arity
   `n+1` and module predicate `decide (i.val = n)`; `lmPrismObject n 1` has arity
   `n` and no module inputs. Thus `lmLeftCutFunctor` has exactly the specified
   object formula, with no restriction on `n`.
3. `lmPrismWords a b c` filters `List.finRange` of the source arity. For an
   algebra output with zero-based index `j`, it keeps precisely the inputs
   `a(j) < i+1 ≤ a(j+1)`. For the final module output, it keeps exactly
   `a(m) < i+1`. The finite-range order is increasing. An input absent from
   every word is discarded. This is the paper's pointed-map formula with all
   non-basepoint indices shifted by one. `lmPrismArrow` bundles these words
   with the admissibility proof, and `lmPrismFunctor` supplies the ordinary
   functor on `Deltaᵒᵖ × [1]`.
4. `lmPrismTheta n` is the identity-ordinal operator from bottom to top. The
   main theorem's third conjunct states its words are exactly `[j.castSucc]`:
   it fixes the algebra inputs and discards the final module input. The next
   conjunct is its naturality square with `lmCutArrow` and `lmLeftCutFunctor`.
5. `lmPrismSimplex` pairs a nerve simplex with the monotone simplex in `[1]`,
   then applies `lmPrismFunctor`. `lmPrism` is the resulting simplicial map on
   the actual product `monoidalSimplexBase ⊗ Δ[1]`. The first two conjuncts
   give its endpoints: `ι₀ ≫ lmPrism = lmLeftCut` and
   `ι₁ ≫ lmPrism = lmCut ≫ lmAlgebraInclusion`.
6. During validation another group landed `def-coef-lm-pointed-projection`.
   I read its full node and module and replaced the local forgetful construction
   with its canonical `lmPointedProjection`, importing
   `Sheaf.CategoryTheory.LMPointedProjection`. It sends an input to the unique
   output containing it, or to zero if absent, using disjointness of output
   words. The pure-algebra base is exactly its restriction along
   `lmAlgebraInclusion`; no second projection is defined.
7. The two approximation conjuncts use the recorded
   `IsOperadicApproximation lmAlgebraPointedBase lmCut` and
   `IsOperadicApproximation lmPointedProjection lmPrism`. This predicate explicitly
   permits a categorical-equivalence/fibration replacement; the main statement
   does not assert that either original map is a categorical fibration.
8. The next two conjuncts use `IsFunctorEquivalence (operadicColourMap … …)`
   for the specified maps on strict colour fibres. This retains the dependency's
   coherent inverse and natural-equivalence convention.
9. The two universal clauses over `r`, `d` and (for the prism) `t` describe
   every simplex above the constant pointed object of arity one. For Cut it
   is precisely the constant simplex at `[1]`; for the prism it is precisely
   one of the two constant pairs `([1],1)` and `([0],0)`. This states the
   asserted discrete singleton/pair fibres in all degrees, including the absence
   of cross-fibre arrows. The following three equations give their images
   `lmAlgebraVertex 1`, `lmVertex (lmAlgebraObject 1)` and
   `lmVertex lmModuleObject`.
10. `IsLMInterval a` is exactly `∀ j, a(j).val = a(0).val + j.val`.
    The four marking clauses say, respectively: `IsLMInert (lmCutArrow a)` iff
    this interval condition (top); `IsLMInert (lmLeftCutFunctor.map a.op)` iff
    that condition and `a(Fin.last m).val = n` (bottom); every `lmPrismTheta`
    is inert (vertical); and `lmPrismArrow a 0 1` is inert iff the interval
    condition (cross). The last equation gives the cross factorization as
    `lmPrismTheta n ≫ lmCutArrow a`. `lmPointedProjection_inert_iff` identifies these
    singleton-word markings with `IsSymmetricInertEdge` for the actual base.

Dependency declarations read and used:

* `Sheaf.CategoryTheory.LeftModuleOperadicEncoding`: `LMWordObject`,
  `lmWordCategory`, `lmAdmissible`, `LMOperadCategory`, `LMAlgebraCategory`,
  `lmAlgebraObject`, `lmModuleObject`, `IsLMInert`, `lmBase`, `lmVertex`, `lmEdge`,
  `lmAlgebraBase`, `lmAlgebraInclusion`, `lmCutWords`, `lmCutArrow`, `lmCutFunctor`,
  `lmCut`, `lmAlgebraVertex`. Its main `CoherentLeftTensoring` declaration was
  read; this lemma intentionally needs no tensoring datum.
* `Sheaf.CategoryTheory.EnhancedDiagramsCones`: Mathlib's nerve conventions and
  `IsFunctorEquivalence` with `AreNaturallyEquivalent` and `IsEquivalenceEdge`.
* `Sheaf.CategoryTheory.OperadicApproximationRestriction`: its full theorem
  signature and docstring were read. The definitions it uses are publicly
  imported from `Sheaf.CategoryTheory.SymmetricOperadicApproximation`, notably
  `IsOperadicApproximation`, `operadicColourMap`, and `IsSymmetricInertEdge`.
  `FinStar`, `finStarBase` and `finStarVertex` come from its public
  `RelativeSymmetricOperadicAlgebras` dependency.
* The stated proof dependencies `InfinityCocartesianMappingCriterion` and
  `InfinityFibrationsOverSimplicialBases` are imported privately, as is
  `OperadicApproximationRestriction`. Mathlib's `Products.Basic` provides
  `Functor.prod'` used in the actual nerve-product construction.

Auxiliary declarations belong to the explicit prism, not independent missing
notions. There are no new nodes or repaired dependency records. The newly landed
`def-coef-lm-pointed-projection` is added to `stmt_deps` and its recorded module
is imported unchanged. Every postponed theorem is listed in `lean.declarations`, carries the
item's blueprint marker and a complete proof plan, and corresponds to a specific
claim in the node's construction or proof: interval admissibility (proof step 1),
identity/composition (step 1), simplicial naturality (step 1),
inert identification (step 4), and
the main theorem (all ten steps). The complete node proof is included verbatim
with wrapping in the main theorem's docstring. All theorem proofs are `sorry`.

Edge cases checked before and after writing:

* `n=0`: the bottom word is the one-input module word; the top has no inputs.
  The vertical quotient has empty output and is inert vacuously.
* `m=0`: the top and cross interval conditions hold for the sole ordinal value,
  while the bottom still requires `a(0)=n`, exactly the singleton final-word
  condition. Repeated ordinal values and empty middle words are permitted.
* Both colour-fibre characterizations quantify over all simplex dimensions.
  A cross edge between the two possible fibre vertices discards the module
  input and therefore is not over the identity of arity one.
* `universe u` is explicit and every other parameter is explicitly bound;
  `AsSmall` retains the same common-universe convention as the dependencies.

Searches for an existing statement or construction:

* `msearch.py ... leansearch "The Cut functor and the left module operad prism
  are approximations of infinity operads"`: eight unrelated truncation and
  simplicial-object hits, no matching statement.
* `msearch.py ... leanfinder "Cut and left-module prism operadic approximation"`:
  eight simplicial primitives, including `SSet.ι₁`, no matching approximation.
* `msearch.py ... loogle "IsOperadicApproximation, lmCut, LMOperadCategory"`:
  zero hits; the service did not know the project-local identifier.
* `msearch.py ... grep "lmCutFunctor|LMOperadCategory|IsOperadicApproximation"
  Mathlib`: zero hits.
* `rg` in the upstream `WeilConjectures/` and item-id search there: no match.
  `rg` in the shared `lean/Sheaf` found the recorded Cut implementation and
  symmetric approximation predicates, but no pre-existing prism statement.
  A final repeat found NH’s newly landed canonical `LMPointedProjection`;
  this delivery now uses it and cites its node.

Validation: the final module compiled cleanly with the prescribed `scompile.py`
wrapper, separately as sandbox and library module, under the default 60-second
limit. There is no `STATEMENT-DISPUTED` flag and no statement correction.

## Second reading by Q87

I read the item node, its source description, the complete Lean module, and the
four dependency records. The node has no ring, scheme, field, characteristic, or
finiteness hypotheses; its objects are finite ordered operators and nerves. The
Lean uses the recorded `LMOperadCategory`, `lmBase`, `lmAlgebraBase`,
`lmAlgebraInclusion`, `lmCutFunctor`, `lmCutArrow`, and `lmCut` from
`Sheaf.CategoryTheory.LeftModuleOperadicEncoding`, the coherent nerve/product
conventions from `Sheaf.CategoryTheory.EnhancedDiagramsCones`, the approximation
predicate from `Sheaf.CategoryTheory.OperadicApproximationRestriction`, and the
canonical `lmPointedProjection` from `Sheaf.CategoryTheory.LMPointedProjection`.

The object and hypothesis list matches the node as follows.

1. The node's $D=N(\Delta^{op})$, $L$, $A$, `LCut`, `Cut`, their ordered
   pointed maps, and the natural quotient are rendered by `lmPrismObject`,
   `lmPrismWords`, `lmPrismArrow`, `lmPrismFunctor`, `lmLeftCutFunctor`,
   `lmLeftCut`, `lmPrismTheta`, and `lmPrism`; the existing `lmCut*` declarations
   supply the pure-algebra construction. The data are explicit, with no chosen
   existence witness. PASS.
2. The source and target arities and colours are exactly the node's formulas:
   `lmPrismObject n 0` has the final module input and `lmPrismObject n 1` is
   pure algebra; `lmPrismWords` uses the displayed inequalities and increasing
   `List.finRange` order. `lmPrismWords_admissible` is the sole postponed
   admissibility assertion. PASS.
3. The functoriality hypothesis is rendered by `lmPrismArrow_id`,
   `lmPrismArrow_comp`, and the `map_id`/`map_comp` fields of
   `lmPrismFunctor`; the naturality assertion is `lmPrismSimplex_natural` and
   the cylinder is `lmPrism`. PASS.
4. The quotient and endpoint clauses are rendered by the first four conjuncts
   of `lm_prism_approximation`: the two endpoint equations, the exact word
   formula `(lmPrismTheta n).hom j = [j.castSucc]`, and its naturality square.
   Quantifiers include `n=0` and all `m,n` and simplex maps. PASS.
5. The two approximation hypotheses are exactly
   `IsOperadicApproximation lmAlgebraPointedBase lmCut` and
   `IsOperadicApproximation lmPointedProjection lmPrism`; the first map is the
   canonical restriction `lmAlgebraInclusion ≫ lmPointedProjection`. The module
   does not add a categorical-fibration assertion to the displayed maps.
   PASS.
6. The two colour-equivalence clauses are exactly the two
   `IsFunctorEquivalence (operadicColourMap ...)` conjuncts. PASS.
7. The Cut fibre clause quantifies over every `r` and every simplex `d`, and the
   prism fibre clause additionally quantifies over every `t`; their right sides
   are exactly the constant vertices/pairs `([1],1)` and `([0],0)`. The final
   three equations identify the images with `lmAlgebraVertex 1`,
   `lmVertex (lmAlgebraObject 1)`, and `lmVertex lmModuleObject`. PASS.
8. The marking conclusion has all four node clauses: top interval iff,
   bottom interval plus endpoint iff, vertical inertness, and cross interval
   iff, followed by the vertical-first factorization
   `lmPrismTheta n ≫ lmCutArrow a`. `IsLMInterval` is the node's formula
   `a(j)=a(0)+j`. PASS.
9. The module includes the auxiliary bridge
   `lmPointedProjection_inert_iff`, whose statement identifies the canonical
   pointed projection's symmetric inert edge with `IsLMInert`; it is used only
   to connect the recorded projection to the explicit singleton-word marking.
   This is a helper belonging to the stated notion, not a second projection.
   PASS.

Edge cases checked: `n=0` gives the module-only bottom object and empty top;
`m=0` makes the top/cross interval condition vacuous while the bottom retains
the endpoint condition; repeated values of a monotone ordinal map and empty
middle fibres are allowed; discarded module inputs are retained in the cross
case; the fibre quantifiers cover every simplex degree; and the explicit universe
`u` is the same universe used by all nerve and `AsSmall` constructions. No field,
scheme, characteristic, or empty-index hypothesis occurs in the source statement.

I read the online 2017 HA PDF at the node's URL: Construction the project server,
Proposition the project server, Construction the project server, Remark the project server, and Definition
the project server. These places impose no target-category hypothesis on the explicit
operators. I also read Remark the project server. Its bottom-first factorization is the
previously reported source slip: for `alpha=(0,1):[1] → [2]` the cross algebra
word is `[0]` but the bottom module word is `[1,2]`, so that bottom factor is
not inert. The node and Lean already use the valid vertical-first factorization.
No correction of the node is needed.

I repeated the existing-definition searches with different queries:

* LeanFinder: "Inverse image of initial segments gives a simplex category prism
  into the associative left module operad, and an operadic approximation".
  Eight hits for simplex, subinterval, and pointed-simplex primitives; no prism
  or approximation theorem.
* LeanSearch: "The simplex category opposite approximates the associative infinity
  operad via the Cut functor". Eight hits for simplex and opposite simplicial
  objects; no operadic approximation.
* Loogle: `SimplexCategory, CategoryTheory.nerveMap`. Eleven generic nerve-map
  declarations; no matching statement. `nerveMap` is already reused here.
* `rg` for `LCut`, `lmPrism`, `lmLeftCut`, `OperadicApproximation`, and
  `IsLMInterval` in Mathlib, `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`,
  and the shared `lean/Sheaf` found the recorded approximation interfaces and
  the downstream coherent-module statement, but no duplicate prism construction
  or theorem. The upstream-name index also has no match.
* A separate interval/consecutive search in Mathlib's simplex-category sources
  found `SimplexCategory.subinterval`, an explicit map constructor, rather than
  a predicate duplicating `IsLMInterval`. I opened that constructor as well.

The msearch responses are recorded in `searches.jsonl`. I opened the recorded
`LMPointedProjection` declaration and verified that it is the canonical
ordered-fibre-forgetting map required by the dependency. There are no new nodes
or dependency modules in this delivery. The added dependency is already landed.

No mathematical mismatch was found. I corrected the worker report's count of
proof steps from nine to ten and added this independent audit. I changed no
statement, hypothesis, dependency, or definition. The node copy's `lean.statement`
is verbatim equal to the theorem signature in the
module, and the prescribed compiler completed both sandbox and library checks
cleanly with only the allowed postponed proofs.
