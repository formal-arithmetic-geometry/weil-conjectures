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

## Second reading by NW

I read the node, its Higher Algebra source places, the complete Lean module, and all four
statement dependencies. The node introduces the ordinary categories and nerves `L` and `A`,
`D = N(Deltaᵒᵖ)`, the explicit `LCut` and `Cut` operators, the quotient `theta`, and the
natural transformation `gamma`. Its conclusion has the two approximation assertions, the two
colour-fibre equivalences, the explicit fibre descriptions and vertex images, and the four
inert-marking clauses with the cross-edge factorization. The Lean renders these through
`lmPrismObject`, `lmPrismWords`, `lmPrismArrow`, `lmPrismFunctor`, `lmLeftCutFunctor`,
`lmLeftCut`, `lmPrismTheta`, `lmPrismSimplex`, `lmPrism`, and the theorem
`lm_prism_approximation`. No hypotheses occur in the source beyond the finite ordered-set
construction; Lean adds no ring, scheme, field, finiteness, or characteristic assumption.

The object and arrow audit is clause-by-clause. `lmPrismObject n 0` has arity `n+1` and its
last input is the unique module input; `lmPrismObject n 1` has arity `n` and no module input.
`lmPrismWords` filters the finite input range by exactly
`a(j) < i+1 ≤ a(j+1)` for middle outputs and by `a(m) < i+1` for the final module output,
with increasing order. Thus it is the source's inverse-image construction under the
zero-based Lean indexing. `lmPrismArrow`, its admissibility theorem, identity and composition
postponements, and `lmPrismFunctor` supply the ordinary functorial construction. PASS.

`lmPrismTheta` is the source's map from the left-module object to the pure algebra object;
the theorem states its words are `[j.castSucc]`, and the following square is its naturality
with `lmCutArrow`. `lmPrismSimplex_natural` and `lmPrism` supply the simplicial cylinder.
The first two theorem conjuncts give the two endpoint restrictions in the source's order.
PASS.

The two approximation clauses are exactly
`IsOperadicApproximation lmAlgebraPointedBase lmCut` and
`IsOperadicApproximation lmPointedProjection lmPrism`; the first map is the canonical
restriction of the recorded `lmPointedProjection`. The statement uses the approximation
predicate's permitted categorical-fibration replacement and does not assert an extra
fibration property of the displayed functors. The two `operadicColourMap` equivalences are
present verbatim. The next universal clauses quantify over every simplex degree (and, for
the prism, every simplex of `Delta[1]`) and characterize precisely the constant Cut vertex
and the two prism vertices `([1],1)` and `([0],0)`, with images `a`, `a`, and `m`. PASS.

The marking clauses match the source: top arrows are inert iff `IsLMInterval`; bottom arrows
are inert iff `IsLMInterval` and `a(Fin.last m)=n`; every vertical `lmPrismTheta` is inert;
and cross arrows are inert iff `IsLMInterval`. The final conjunct is exactly the
vertical-first factorization through `lmPrismTheta n`. The bridge
`lmPointedProjection_inert_iff` identifies the recorded projection's inert edges with the
singleton-word predicate used by these clauses. PASS.

I checked the edge cases `n=0`, `m=0`, `r=0`, empty middle fibres and discarded inputs.
For `n=0`, the bottom object is module-only and the top object is empty; for `m=0` the
top/cross interval condition is vacuous while the bottom endpoint condition remains. The
fibre clauses quantify all degrees, and the explicit universe `u` is shared by all nerves and
`AsSmall` transports. No edge case is excluded.

I read the source online at Higher Algebra Construction the project server and Remark the project server, and
Definition the project server for approximation. The source gives the same downward-closed-subset
bijection, the displayed block formula, the quotient sending `n+1` to the basepoint, and the
claim that `gamma` is an approximation. I also checked the source's inert-marking discussion;
the known bottom-factorization slip is avoided by the node's vertical-first factorization.

I repeated searches with independent queries. LeanFinder for `LM prism approximation Cut LCut
operadic` returned only unrelated optimization and simplex primitives; Loogle for
`IsOperadicApproximation lmPrism` returned no hits because the identifier is project-local;
grep over Mathlib returned no `lmPrism`, `LCut`, or `IsLMInterval`. Searches over
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the shared `lean/Sheaf` found only the
recorded definitions and this module, with no duplicate construction or theorem. The exact
recorded dependency declarations in `LeftModuleOperadicEncoding`, `EnhancedDiagramsCones`,
`OperadicApproximationRestriction`, and `LMPointedProjection` were opened and match their
node statements.

No mismatch was found. I changed no definition or theorem statement; only the node's delivery
metadata records NW as the second reader. The node copy's `lean.statement` remains verbatim
equal to the theorem signature, and all postponed declarations retain their source and
`(blueprint: lem-coef-lm-prism-approximation)` docstrings.
