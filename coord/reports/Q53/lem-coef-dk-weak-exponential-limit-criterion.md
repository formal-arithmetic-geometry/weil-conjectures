## Worker report

The module `Sheaf.CategoryTheory.DkWeakExponentialLimitCriterion` states
`CategoryTheory.DkWeakExponential.dk_weak_exponential_limit_criterion` with `sorry`.
All helper definitions have real data. They belong to this node's compatible-span and
model-derived-cocone interface and are listed in `lean.declarations`.

I read the node and both statement dependencies, including their full recorded signatures,
and the dependency modules `SimplicialProjectiveModelCalculus` and
`SimplicialLocalizationComparisonCalculus`. I also read `BergnerModelData` in
`CoherentNerveComparison`, `SCat` and its category instance in
`CoherentNerveInfrastructure`, the Kan--Quillen weak-equivalence structure, Mathlib's
localization construction and binary-product API. There is no repair note for this item.

Source checked: HTT, downloaded from the node's Harvard URL, Definition A.3.6.1,
Proposition A.3.6.15 and its proof (printed pages 897, 902--903). The source specifies
homotopy product by the product universal property after localization. It has the
same two variances and natural compatible spans. The node's expanded proof repairs the
source's frame construction; the twelve steps are included in the theorem docstring.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Fixed small simplicial categories are the existing `CoherentNerve.SCat.{u}`. Objects,
  mapping simplicial sets, and ordinary index objects live in universe `u`; no independent
  smaller testing universe is introduced. The ambient category lives in the larger universe.
- The supplied `B : BergnerModelData.{u}` is the dependency's DK model, including its
  characterization of weak equivalences and its small limits and colimits. No new model
  or enrichment notion is introduced. The theorem is valid for any such model data.
- Combinatoriality is the first conjunct, explicitly
  `@CombinatorialModelCategory.{_, _, u} SCat.{u} inferInstance B.model`; the presentation
  universe is fixed to `u`, not left as a universally quantified extra universe.
- Trivial fibrations are the intersection of `B`'s fibration and weak-equivalence classes.
  The second conjunct characterizes this intersection by `Function.Surjective p.obj`
  and `trivialFibrations SSet (p.map x y)` for every pair of source objects. The latter
  uses the recorded realization-based Kan--Quillen weak-equivalence structure and
  standard Kan fibrations (the two scopes are opened explicitly).
- The third conjunct characterizes cofibrations by `HasLiftingProperty i p` against
  every functor satisfying exactly that surjective/local-trivial condition.
- For every `J : Type u` with `SmallCategory J`, the fourth conjunct supplies a
  `ModelCategory (J ⥤ SCat)` with both weak equivalences and fibrations equal to the
  objectwise classes of the same `B`.
- `multiplication B` is Mathlib's chosen Cartesian product bifunctor, using `B.complete`.
  The fifth conjunct sends every poset-indexed model-derived colimit cocone through
  its functor at a fixed `D`. Strict products compute derived Cartesian products here,
  as explained by proof step 3; no cofibrancy/fibrancy restriction on `D` is imposed.
- `IsDerivedColimit B c` is the exact dual of the dependency's `IsDerivedLimit`, using
  opposite weak equivalences and opposite fibrations. Unfolding it gives a replacement
  from a projectively cofibrant diagram, an ordinary colimit of that replacement, and
  the weak-equivalence test for its comparison into the given apex. This is a model
  homotopy colimit rather than an ordinary colimit of the homotopy category.
- A poset `K` with `OrderTop K` is equivalently its full lower subposet obtained by
  deleting `⊤`, together with that newly adjoined largest element. `belowTop K` is
  `a ≠ ⊤`; no inhabitedness of this subposet is required.
- `intervals K` is the existing Mathlib full-subcategory construction applied to
  `(Kᵒᵖ × K)` with predicate `b ≤ a.unop`. Thus it has exactly the source's order.
- The binders `X`, `Y : K ⥤ SCat`, `Z : Kᵒᵖ ⥤ SCat` and
  `P : (intervals K).FullSubcategory ⥤ SCat` retain all four objects/diagrams.
  `productDiagram B Y Z` is the composite of the full inclusion, `Z.prod Y`, and
  Mathlib's uncurried Cartesian multiplication.
- The natural transformations `p : P ⟶ productDiagram B Y Z` and
  `q : P ⟶ (Functor.const _).obj X` express both span legs and their functoriality
  in both coordinates, not merely unrelated objectwise evaluation maps.
- `localizedProductCone B (p.app a)` has apex `[P(a,b)]` and projections induced by
  `p` and the two strict product projections. The binder `hp` requires `IsLimit` for
  this binary cone at every pair, exactly the homotopy-product condition of A.3.6.1.
- At each diagonal `(a,a)`, `IsWeakExponential` requires for every small `T` an actual
  limiting binary cone with factors `[T]` and `[Y(a)]`. Its induced function on hom sets
  composes the unique product map `(f, id)` into `[P(a,a)]` with `[q]`; it is required
  to be bijective. This is the displayed source bijection, including its prescribed
  evaluation map. Requiring a limiting cone rules out vacuous universal testing.
- `topCocone Y` has apex `Y.obj ⊤` and exactly the arrows `Y.map (a ≤ ⊤)`.
  Its model-derived colimit condition is the antecedent.
- `topCone Z` has apex `Z.obj (op ⊤)` and exactly the opposite arrows to `Z(a)`.
  The conclusion uses the dependency's `SimplicialLocalizationCalculus.IsDerivedLimit`
  with `B`'s weak equivalences and cofibrations. It tests against an injectively
  fibrant replacement and its strict limit, so is the full model-category conclusion.

Dependency declarations used:

- `Sheaf.CategoryTheory.SimplicialLocalizationComparisonCalculus`:
  `CategoryTheory.SimplicialLocalizationCalculus.IsDerivedLimit`, and the imported
  `CategoryTheory.BergnerModelData`, `CategoryTheory.CoherentNerve.SCat`.
- `Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus`: its recorded model and
  enrichment interfaces, and the shared `HomotopicalAlgebra.CombinatorialModelCategory`.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.weakEquivalenceStructure` and its scoped instance.
- Mathlib: `MorphismProperty.Q`, `BinaryFan.mk`, `IsLimit.lift`, `prod.functor`,
  `ObjectProperty.FullSubcategory`, `ObjectProperty.ι`, `Functor.prod`, `Functor.uncurry`.

All locally recorded, stated proof dependencies are imported. The proof-only modules
are ordinary imports. The other proof dependencies have no recorded module in the read
snapshot, so no speculative imports were added.

Edge cases checked: `K` the singleton top gives empty `K₀`, and both constructions
retain empty (co)limits; an arbitrary empty poset is allowed in the multiplication
clause. Empty simplicial categories, empty mapping sets and maps with empty source
object type are allowed. The trivial-fibration test retains object surjectivity in
those cases. No Kan, cofibrancy, fibrancy or nonemptiness assumptions are added to the
spans or their test objects. Product cones exist explicitly in the weak-exponential
condition; it is not vacuous when the test hom set is empty. A poset with a preexisting
largest element still represents exactly the complement of the chosen top plus top.

Searches performed through `msearch.py` (saved in `searches.jsonl`):

- LeanFinder: `Compatible weak exponentials turn homotopy colimits into homotopy limits
  in simplicial categories`: eight results, on simplicial-object (co)limits,
  `hoFunctor` preserving products and Dold--Kan; none states this criterion.
- Loogle: `"ModelCategory", "exponential"`: zero hits.
- Mathlib grep: `WeakExponential|weak.exponential|Bergner`: zero hits.
- LeanSearch: `Cartesian products preserve homotopy colimits of simplicial categories
  and compatible weak exponentials give homotopy limits`: eight generic product,
  simplicial-object and `hoFunctor` results; none is this statement.
- Direct `rg` in upstream `WeilConjectures`, the project `lean/Sheaf`, and upstream names:
  no declaration of this criterion or weak exponentials. The only two project hits are
  proof-docstring citations in `ProjectiveDiagramSimplicialDescent`, not declarations.
  Further `rg` identified the existing derived-limit and injective-limit interfaces;
  the former is used directly, with its dual for the colimit clause.

No statement correction, dependency repair, or independent new notion is needed.
No STATEMENT-DISPUTED fault remains. The file compiles cleanly through `scompile.py`;
only the requested main theorem is postponed.

## Second reading by Q53

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
