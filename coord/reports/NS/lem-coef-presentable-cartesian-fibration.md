## Worker report

Item: `lem-coef-presentable-cartesian-fibration`.
Module: `Sheaf.CategoryTheory.PresentableCartesianFibration`.
Declaration: `SSet.Presentability.presentable_cartesian_fibration`.
The only postponed declaration is this theorem, with proof `sorry`. Its docstring
records the node's eight proof steps and all their named inputs. No definition,
helper theorem, dependency module, or mathematical statement correction is introduced.

Source checked: Gepner--Haugseng--Nikolaus, *Lax Colimits and Free Fibrations in
infinity-Categories*, https://arxiv.org/html/1501.02161v3, Definition 10.1,
Remark 10.2, Theorem 10.3 and its proof, including Lemma 10.7 and Proposition 10.5.
Definition 10.1 supplies presentable fibers and right-adjoint transport; the proof
explicitly establishes accessibility of the projection as well as of the total category.
The theorem concerns arbitrary presentable bases, with no globally small-base assumption.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The universe convention of `def-coef-complete-algebroid` is rendered by independent
  `universe u v`, with `E B : SSet.{max (u + 1) v}`. Small always means `u`.
  The classifying diagram lives in `max (u + 1) v + 1`, allowing its values to be
  categories in `max (u + 1) v`. The monoidal categories in the opening reference
  supply the context and universe convention; no monoidal structure occurs in
  this general fibration theorem, so none is assumed of E, B, or p.
- The infinity categories E and B have explicit `[Quasicategory E]` and
  `[Quasicategory B]` binders, and their projection is `(p : E ⟶ B)`.
- Cartesian fibration means exactly `(hp : Enhanced.cartesianFibration p)`, the
  published inner-fibration and Cartesian edge-lifting predicate reexported by
  the dependency's recorded `InfinityFibrationsOverSimplicialBases` module.
- The coherent classifying functor is the simplicial map `G` from the opposite
  of the degreewise lift of B to the existing `Enhanced.CatInfinity`.
  `(hclass : Enhanced.IndCartesianClassification p G)` is the existing general
  classification predicate, despite its Ind-prefixed name: its signature has
  arbitrary E, B, p and G and no presheaf or Ind hypotheses. It specifies the
  entire strict diagram of Cartesian sections on every simplex, with its
  actual restriction maps and the coherent equivalence to G on the canonical
  last-vertex resolution. Thus G is tied to p on all higher simplices.
- Presentability of B is `(hB : IsPresentable.{u, v} B)`.
- Presentability of every fiber is `hfibers`, applying that same predicate to
  every `compactDiagramValue G b`. These are the classifying values, identified
  with the actual fibers of p by `hclass`. The explicit quasicategory witness
  is `compactCatQuasicategory (G.app _ b)`, which comes from the CatInfinity
  vertex rather than an additional assumption. Quantification over all vertices
  of the opposite lifted B is exactly quantification over the vertices of B.
- Every restriction is a right adjoint: `hR` quantifies over every edge e of
  the opposite lifted base and asserts existence of a left adjoint L to the
  actual `compactDiagramArrow G e`, with `Nonempty (CoherentAdjunction L ...)`.
  The source of L is the target fiber of that contravariant arrow, and its
  target is the arrow's source fiber. `CoherentAdjunction` retains the full
  unit, counit, triangle simplices and mapping-space universal properties.
  There is no arbitrary independent map standing in for G(e).
- The single infinite regular cardinal in the filtered-colimit hypothesis is
  `hG : ∃ κ : Cardinal.{u}, κ.IsRegular ∧ ...`. Mathlib's `IsRegular` includes
  infinitude, so this is precisely the cardinal required by the node.
- Every small kappa-filtered diagram is included by the binders I, hI,
  `IsSmall.{u, max (u + 1) v + 1} I` and `@IsKappaFiltered κ I hI`, followed
  by every diagram F into the lifted B. The higher universe permits composition
  with G; it does not enlarge the small universe or assume the base is small.
- Every colimit cocone is tested: the t binder and `Enhanced.IsColimiting F t`
  give its actual coherent transformation, not just its colimit apex.
- The canonical limit cone is the existential pair o, s with
  `Enhanced.IndOppositeCocone F t o`, `Enhanced.IsImageCone G ... o s` and
  `Enhanced.IsLimiting ... s`. The first predicate fixes both the opposite
  apex and entire reversed prism, and the second fixes both postcomposed
  coordinates. Consequently s has apex G(colim F) and exactly the induced
  cone legs. No unrelated limiting cone or arbitrary equivalence replaces
  the canonical comparison in the statement.
- The first conclusion is `IsPresentable.{u, v} E`, relative to the original
  small universe. The second is `∃ μ : Cardinal.{u}, μ.IsRegular ∧
  PreservesKappaFiltered μ p`, which asserts preservation by p itself of
  all existing small mu-filtered colimiting cocones. This is the requested
  accessibility, not merely accessibility of the source or some unrelated map.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CompleteAlgebroid`:
  `SSet.Enhanced.Algebroid.completeCategory` and `IsPresentablyMonoidal` were
  read to check the universe convention; no second algebroid notion is defined.
- `Sheaf.CategoryTheory.PresentableInfinityCategory`:
  `SSet.Presentability.IsPresentable`, `IsSmall`, `IsKappaFiltered`, and
  `PreservesColimitsIn`, including the complete source definitions of
  accessibility, compactness and small colimits.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases` publicly
  reexports `SSet.Enhanced.cartesianFibration` from `InfinityFibrations`;
  that definition and the fiber and Cartesian-edge definitions were read.
- `Sheaf.CategoryTheory.EnhancedCartesianFibration`:
  `SSet.Enhanced.CatInfinity` and its core-enriched subcomplex construction;
  classification uses its existing Cartesian section and strict-diagram data.
- `Sheaf.CategoryTheory.SmallRightAdjointDiagramCompactModel`:
  `SSet.Presentability.compactDiagramValue`, `compactCatQuasicategory`,
  `compactDiagramArrow`, and `PreservesKappaFiltered`. The diagram arrow uses
  its published endpoint transports, not an edge with silently identified types.
- `Sheaf.CategoryTheory.IndPresheafFibrationAccessibility`:
  `SSet.Enhanced.IndCartesianClassification` and `IndOppositeCocone`.
  Both are general in the base and total-category universes. Their full
  signatures and defining equations were checked, not just their names.
- `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`:
  `HomotopicalAlgebra.ModelInfinity.CoherentAdjunction`.
- `Sheaf.CategoryTheory.InfinityLimitsProductsPullbacks`:
  `SSet.Enhanced.IsImageCone`, which fixes the whole postcomposed cone.

The five already-landed nodes carrying the last interfaces are added to
`stmt_deps`: `def-cbc-enhanced-cartesian-fibration`,
`lem-coef-small-right-adjoint-diagram-compact-model`,
`lem-coef-ind-presheaf-fibration-accessibility`,
`lem-coef-model-infinity-derived-adjunction`, and
`lem-coef-infinity-limits-products-pullbacks`. Only `lean` and these additions
to `stmt_deps` change in the node. No dependency's record is modified.

The stated proof-dependency modules are imported. The proof inputs without a
published Lean record at writing time are
`lem-coef-presentable-infinity-adjoints`,
`lem-coef-infinity-grothendieck-limits-colimits`,
`lem-coef-infinity-yoneda-presheaf-limits`,
`lem-coef-spaces-small-colimits-universe`,
`lem-coef-cocartesian-straightening`, and
`lem-coef-accessible-infinity-pullback`; no import is invented for them.
They are not needed to type the statement. There is no import cycle.

Edge cases checked:

- Empty I is excluded by the mathematical filteredness condition itself:
  `IsKappaFiltered` tests the empty source diagram, requiring a cocone vertex.
  No extra `Nonempty` hypothesis is imposed or omitted.
- An empty base cannot satisfy `IsPresentable`, since it lacks the empty
  colimit. This agrees with the source; no artificial inhabited-base assumption
  is introduced. Empty fibers likewise cannot be presentable.
- A point base reduces the assertion to presentability of its fiber. For a
  constant diagram with terminal-category fibers, the projection is equivalent
  to the identity of B and the statement gives its expected accessibility.
- The rank kappa can be aleph_0; there is no uncountability assumption in the
  theorem. The larger uncountable ranks only occur inside its proof plan.
- B, E and their fibers can be large in u. In particular, the universe v is
  independent and is never equated with u or u+1. Smallness of a simplicial
  model is not substituted for essential/local smallness of a presentable category.
- The filtered-colimit condition tests every t, including arbitrary equivalent
  representatives of colimit cocones, and preserves their entire canonical cones.

Searches made with the prescribed tools (2026-10-17):

- `msearch.py ... leansearch "A presentable Cartesian fibration has presentable
  total infinity category and accessible projection"`: eight hits, including
  `CategoryTheory.Functor.IsFibered`, its constructors and ordinary-category
  presentability declarations. None states the quasicategorical theorem.
- `msearch.py ... leanfinder "Cartesian fibration with presentable infinity
  categorical base and fibers and right adjoint transports has presentable
  total category and accessible projection"`: eight hits, on ordinary
  adjunctions, locally presentable presheaf categories and compact generators.
  No matching infinity-categorical fibration statement.
- `msearch.py ... loogle "CategoryTheory.Functor.IsFibered,
  CategoryTheory.IsLocallyPresentable"`: zero hits.
- `msearch.py ... grep "presentable.*fibration|fibration.*presentable|
  PreservesKappaFiltered" CategoryTheory`: zero Mathlib hits.
- `rg` for the item id, `presentable_cartesian_fibration`, and both orderings
  of presentable/Cartesian fibration in `WeilConjectures/` and `lean/Sheaf/`:
  no existing declaration. The upstream-name index likewise has no matching name.
- Read Mathlib `CategoryTheory/FiberedCategory/Fibered.lean:48-67`,
  `CategoryTheory/Presentable/LocallyPresentable.lean:30-53` and
  `CategoryTheory/Presentable/Adjunction.lean:27-58` to verify the returned
  candidates are ordinary-category notions and cannot be used as this theorem.
- Source searches in the project's Lean found and reused the general
  `IndCartesianClassification`, `IndOppositeCocone`, coherent diagram-value
  and arrow functions, `IsImageCone`, and the filtered-preservation predicate.
  Therefore no new definition node is needed.

Validation: `scompile.py NS lem-coef-presentable-cartesian-fibration
lean/Sheaf/CategoryTheory/PresentableCartesianFibration.lean` compiled the
sandbox and named module cleanly (8.0 s and 8.3 s respectively). The first
attempt exposed that Unicode lambda is reserved as a binder identifier;
renaming the existential rank to mu resolved it. Every line is at most
100 characters. All variables and universes are explicitly bound.
No disputed statement or source discrepancy was found.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
