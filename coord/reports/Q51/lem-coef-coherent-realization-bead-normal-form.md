## Worker report

The module states `SSet.CoherentBeads.coherent_realization_bead_normal_form` for the
specified `SSet.PinchedCube.rigidification`, with one postponed theorem and explicit
helper constructions. Its data do not depend on a mere existence choice. The module
uses the actual coherent-simplex cocones and levelwise enriched composition; it
constructs neither a different realization nor an arbitrary comparison functor.

Source read: Riehl--Verity, Recognizing quasi-categorical limits and colimits in
homotopy coherent nerves, arXiv:1808.09834v3, Section 5.1, printed pp.26–30,
Definitions 5.1.1 and 5.1.4, Example 5.1.7, Definition 5.1.8, Lemma 5.1.9,
Definition 5.1.11 and Proposition 5.1.12. The source's strict bead shapes describe
nondegenerate atomic arrows. The node also includes their weak-flag degeneracies.
No correction to the node's natural statement is required.

Clause-by-clause translation:

- Small simplicial sets and arbitrary degree: every `K L : SSet.{u}` and `r : ℕ`
  is explicit, with arbitrary universe `u`. No Kan, quasicategory or boundedness
  hypothesis is introduced.
- Objects are exactly the vertices: the first conjunct is bijectivity of the
  canonical vertex map, explicitly the object map of
  `PinchedCube.coherentSimplexUnit.app ⦋0⦌ ≫ PinchedCube.rigidification.map
  (SSet.yonedaEquiv.symm s)` at `ordinalVertex 0 0`. The next conjunct identifies every
  coherent-simplex object with its vertex in `K`, using `simplexVertex s j`.
- A generator is a positive-dimensional nondegenerate simplex and a weak flag:
  `Bead` has `dim`, `positive : 1 ≤ dim`, `simplex : K.nonDegenerate dim`, and
  `flag : Flag dim r`. `Flag` is the actual mapping nerve simplex, so its subsets
  are weakly increasing. `first` is the two endpoints; `last` is the full interval.
- Endpoints are the initial and final vertices: `Bead.source` and `Bead.target`
  apply the existing simplex cocone to `ordinalVertex dim 0` and `Fin.last dim`;
  the theorem's second conjunct identifies these with the stated simplex vertices.
- The directed graph is `Graph` with `beadQuiver`, whose arrows are precisely beads
  with those endpoint equalities. `Graph` is a type synonym of the actual object
  set, canonically bijective to `K₀` by the first conjunct. This avoids imposing
  the bead graph's quiver on the enriched category itself.
- The ordinary degree category is free on that graph: `Quiver.Path x y` is a finite
  composable word, and `Function.Bijective (wordValue (x := x) (y := y))` gives
  existence and uniqueness for each actual mapping simplex. `wordValue` sends
  `nil` to the enriched identity and `cons` to actual enriched composition.
- A bead is nondegenerate exactly when the flag has no repetitions: the fourth
  conjunct uses the mapping simplicial set's `nonDegenerate r` and injectivity
  of `j ↦ (b.flag.obj j).I`. In a monotone chain this is precisely strictness.
- Simplicial operators: `restrictFlag θ` is the existing mapping simplicial set's
  operator. The sixth conjunct says its entries are exactly `T_{θ(j)}`. The fifth
  conjunct identifies its value with the operator on `flagValue s t` in the
  actual realization. This applies to arbitrary flags, not only endpoint/full
  flags, so faces with new junctions or smaller support are included. Combined
  with bijective word evaluation, this says to evaluate the restricted flag and
  take its unique word. Operators on general words act letterwise and compose,
  because `wordValue` uses the actual simplicial enriched composition. In
  particular `θ = σ i` repeats an entry, including degeneracies of beads.
- The sole hypothesis on `i` is exactly degreewise injectivity,
  `∀ d, Function.Injective (i.app d)`. Under it the conclusion gives injectivity
  of the actual object function and of every degree of every mapping map.
- The image is the free subcategory on the specified vertices and beads:
  `InImage i (wordValue p)` retains preimage objects, an actual arrow, both endpoint
  equalities and equality of its image (as `HEq` to permit dependent endpoints).
  The final iff requires endpoints in the canonical image of `K₀` and
  `WordLabelsIn i p`. This recursive predicate tests exactly the nondegenerate
  simplex label of every bead against the corresponding `Set.range (i.app _)`.
- Empty words: `WordLabelsIn i nil = True`, while the endpoint membership remains
  in the iff. Thus an identity at an excluded vertex is not spuriously in the
  image. For `nil` both endpoints coincide, so the two endpoint tests reduce to
  the one vertex test in the node.

Dependency declarations read and used:

- `Sheaf.AlgebraicTopology.PinchedCubeLatching`:
  `SSet.PinchedCube.coherentSimplex`, `rigidification`, `coherentSimplexUnit`,
  and `pinched_cube_latching`. The first is Mathlib's subset-poset thickening;
  the second is its Yoneda left Kan extension with the actual unit cocones.
- The simplex cocone is written directly as
  `PinchedCube.coherentSimplexUnit.app _ ≫ PinchedCube.rigidification.map
  (SSet.yonedaEquiv.symm s)`. Its degree-zero object map gives vertices.
  These are the underlying expressions used by the straightening helpers,
  without importing their downstream theorem or defining another copy.
  The only statement dependency remains `lem-coef-pinched-cube-latching`.
- Proof imports: `Sheaf.AlgebraicTopology.SimplicialCategoryDegreewiseColimits`
  supplies `CategoryTheory.CoherentNerve.simplicial_category_degreewise_colimits`;
  `Mathlib.AlgebraicTopology.SimplicialSet.Skeleton` supplies the exact Mathlib
  match `SSet.relativeCellComplexOfMono` (lines 428–446) for
  `lem-coef-infinity-monomorphism-boundary-cells`. The interval-lifting module
  is reached through the pinched-cube import, supplying
  `SSet.Bergner.simplicial_interval_lifting` and the enriched colimits.
- Mathlib `SimplicialThickening.Path`, its interval subset field `I`, its nerve,
  `SSet.nonDegenerate`, `Quiver.Path`, and the existing enriched `hom`, `eId`,
  `eComp` are reused. The helper `Graph` changes only the type's quiver instance.

Searches (earlier attempt retained in searches.jsonl, then inspected again):

- `msearch.py leanfinder`: “Homotopy coherent realization has unique words of
  beads indexed by nondegenerate simplices and flags of endpoint-containing
  subsets” returned subset-path/ordinary-path/strict-Segal-core results, no
  coherent-realization theorem.
- `msearch.py loogle`: `"SimplicialThickening"` returned the subset-poset simplex
  API; its source was read, but it supplies no arbitrary-simplicial-set normal form.
- `msearch.py grep`: `computad|necklace|bead|rigidification` in AlgebraicTopology
  returned zero hits, also on rerun.
- `msearch.py leansearch`: “Homotopy coherent realization free category generated
  by beads of nondegenerate simplices and flags of subsets” returned `SSet.toTop`,
  ordinary free-category constructions and simplex-category presentations, no match.
- `rg` in upstream WeilConjectures and project Sheaf for the item id and
  `CoherentBeads|coherent.realization|bead` found no existing theorem. Project
  searches did reveal the already-landed `Straightening.simplexInclusion` and
  `Straightening.vertex`, whose underlying unit-and-rigidification expressions are used directly
  after the cycle repair below. Exact new-name searches in
  Mathlib, upstream and project found no collision.

Edge cases checked: the empty simplicial set has no vertices or words with endpoints;
there is no omitted nonempty hypothesis. Discrete simplicial sets have only empty
words. At degree zero, the first and last flag are the same, forcing a bead's
support to consist of its two endpoints, so only dimension-one simplices generate;
flag injectivity is automatic and every zero-simplex is nondegenerate. Dimension
zero is explicitly excluded from beads, preventing identities from becoming
letters. Repeated flag entries are allowed and detected as degeneracies. A
nondegenerate simplex can have coincident endpoint vertices, so loops and
noninjective simplex attaching maps are allowed. Empty subcomplexes, identities
outside a subcomplex, arbitrary-dimensional simplicial sets, and arbitrary
ordinal operators are all retained. Site/coefficient universe restrictions are
not involved: every construction stays in the arbitrary simplicial-set universe.

The nine-step natural-language proof plan is included in the theorem docstring.
No theorem is proved and no definition contains `sorry`. There are no new DAG
nodes, dependency repairs, disputed statements or statement corrections.

## Return repair

The retained packet was dry-run before editing. It reproduced the independent
review's diagnostic: incremental DAG validation found a cycle through the added
`lem-coef-right-straightening-fiber-comparison` statement dependency. The earlier
report's claim of acyclicity was incorrect: the actual path is
`lem-coef-right-straightening-fiber-comparison` →
`lem-coef-contravariant-slice-model` →
`lem-coef-coherent-inner-anodyne-equivalences` → this item.

Removed that added dependency and its Lean import. Every use of the
straightening simplex/vertex helpers is replaced by its exact underlying
`coherentSimplexUnit` and `rigidification.map` expression from the already
recorded pinched-cube dependency. No duplicate helper definition is introduced.
The natural statement, proof plan and original statement dependencies are
unchanged. All bead constructions and all seven theorem conjuncts retain the same
objects and maps by unfolding the two removed helpers. The legacy import style
is retained because the recorded degreewise-colimits proof dependency is not
yet a Lean `module`; an attempted module header was rejected by the compiler
and removed.

Validation: the revised file is compiled using the required scompile.py wrapper;
the final dry run and delivery use the current main branch through deliver2.py.

## Second reading by Q51

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
