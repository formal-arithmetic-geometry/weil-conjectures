## Worker report

The module `Sheaf.AlgebraicTopology.JoyalHomotopyExponentials` states
`SSet.joyal_homotopy_exponentials` and defines two real-data helpers,
`SSet.localizedProductFan` and `SSet.localizedEvaluation`. There is one postponed
theorem and no postponed definition, new node, dependency module, or statement
correction. The item's node copy changes only `lean`.

Hypotheses and clauses, in the order of the natural-language statement:

- “Use the Joyal model structure and categorical equivalences”: the binder
  `M : HomotopicalAlgebra.ModelCategory SSet.{u}` and `hJoyal` bind the
  weak-equivalence class to the exact enlarged-universe testing condition in
  `SSet.exists_joyal_model_structure`. The theorem uses only that class, so other
  model-structure choices with the same class cannot affect its conclusion.
  This is an explicit interface for the structure already supplied by that
  dependency, not a new mathematical assumption. No model is chosen from a
  bare existence assertion to define data.
- “Use the coherent-nerve adjunction”: `D : CoherentNerveComparisonStatement.{u}`
  is the precise dependency interface; `D.rigidification` is its colimit
  extension of the prescribed coherent simplices. Its adjunction and simplex
  formulas are read in `CoherentNerveComparison.lean`. No private rigidification
  or alternative nerve is defined here.
- “Fixed nested universes” and `def-cbc-enhanced-diagrams-cones`: the explicit
  `universe u v`, `SSet.{u}` and its localization in `Type (u + 1)` render
  small simplicial sets and categories in the larger universe. Enlarged
  categorical-equivalence tests use `max u v`, exactly as in the Joyal
  dependency. `Sheaf.CategoryTheory.EnhancedDiagramsCones` is imported directly.
  Its full source and node were read: it uses Mathlib's `SSet.Quasicategory`,
  standard simplices, horns, degreewise cartesian monoidal structure and
  `(ihom K).obj Q` directly. These are the same objects used here; the
  additional mapping-space and cone constructions of that dependency do not
  occur in this statement. No algebroid assumption or substitute convention
  is introduced.
- “Ordinary localization” and its Hom sets: for
  `W = M.categoryWithWeakEquivalences.weakEquivalences`, these are Mathlib's
  `W.Localization` and morphisms between `W.Q.obj` objects. They are the formal
  arrow-inverting ordinary localization, not `SSet.hoFunctor` and not the
  ordinary homotopy category of a single quasicategory. `hoFunctor` occurs
  exclusively in the categorical-equivalence test.
- “For simplicial sets K,L”: both binders range over every `SSet.{u}`, without
  fibrancy, nonemptiness or finite-size restrictions.
- “Their degreewise product represents the categorical product”: the first
  conjunct is `∀ K L, Nonempty (IsLimit (localizedProductFan W K L))`.
  Mathlib's `K ⊗ L` is the degreewise cartesian product. The helper is exactly
  `BinaryFan.mk (W.Q.map (fst K L)) (W.Q.map (snd K L))`, so the specified
  projections as well as the vertex are retained.
- “The natural functor C[K×L] → C[K]×C[L] is a DK equivalence”: the second
  conjunct supplies a limiting `BinaryFan` `c` in the existing ordinary category
  of small simplicial categories, and asserts `DwyerKanEquivalence` of
  `h.lift (BinaryFan.mk (D.rigidification.map (fst K L))
  (D.rigidification.map (snd K L)))`. The limit property uniquely determines
  the target product and the lift is uniquely characterized by its two actual
  rigidified projections. It is not an arbitrary enriched functor or a
  weak-equivalence replacement of the comparison. This universal-product form
  is equivalent to the standard coordinatewise product, up to the unique
  projection-preserving isomorphism. DK equivalence is invariant under that
  isomorphism. Thus the existential product cone is just a way of supplying the
  product that the statement already denotes; it imposes no extra hypothesis
  and loses no information about the map. Naturality follows from its two
  projection equations and uniqueness of product pairing.
- “For every quasicategory Q, Fun(K,Q)_n = Hom(K×Δ[n],Q)”: the object is the
  existing Mathlib internal hom `(ihom K).obj Q`. I read its implementation in
  `FunctorToTypes.rightAdj` and the functor-Hom equivalence. This is the existing
  simplicial function object used by both statement dependencies. No new
  definition of Fun is made.
- “This is a quasicategory”: the third conjunct has the exact implication
  `Q.Quasicategory → ((ihom K).obj Q).Quasicategory ∧ ...`.
- “Evaluation induces natural bijections [X,Fun(K,Q)]_J ≅ [X×K,Q]_J”: for every
  `X`, the final clause is `Function.Bijective (localizedEvaluation W X K Q h)`.
  Its domain and codomain are exactly those two Hom sets, in that order. The
  helper first uses the limiting product cone for `Fun(K,Q),K` to pair
  `W.Q.map (fst X K) ≫ f` with `W.Q.map (snd X K)` and then composes with
  `W.Q.map ((β_ ((ihom K).obj Q) K).hom ≫ (ihom.ev K).app Q)`.
  This is precisely localized evaluation after `f × 1_K`, including for arrows
  `f` that are represented by arbitrary localization zigzags. The binder `h`
  is not an extra assumption: the first conjunct supplies its inhabitant for
  this pair, and the last clause holds for every such inhabitant. Any two are
  equal by uniqueness of limit structures. Bijectivity gives the inverse
  currying bijection.
- “Natural” and “represents [Q]^[K], not just an ordinary hQ exponential”:
  the last clause is the exponential universal property with the specified
  evaluation. For any localized arrow `a : [X'] → [X]`, define its product
  with `1_[K]` by the unique product pairing. Composing a transpose with that
  pairing agrees with transposing `a ≫ f`: both pairings have the same two
  projections. Postcomposition in Q and precomposition in K commute with
  the actual simplicial evaluation by the existing internal-Hom naturality;
  uniqueness of transposes gives the corresponding naturality squares.
  Those squares persist on inverted equivalences. Hence this universal
  property entails the stated naturality in every variable; an additional
  family of unconstrained equivalences would be weaker. Every Hom set in
  the conclusion is in `W.Localization`, so the ordinary-hQ replacement is
  explicitly excluded by its type.

Dependency declarations used:

- `Sheaf.AlgebraicTopology.JoyalModelStructure`:
  `SSet.exists_joyal_model_structure`; its displayed testing interface is used
  verbatim, including `uliftFunctor.{v,u}`, `max u v`, restriction, and h.
- `Sheaf.CategoryTheory.CoherentNerveComparison`:
  `CategoryTheory.CoherentNerveComparisonStatement`, its `rigidification`
  field, and `CategoryTheory.DwyerKanEquivalence`; `SCat` and `underlying`
  come from its imported `CoherentNerveInfrastructure`.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: the shared Mathlib simplicial
  primitives and internal hom explicitly named in its module documentation;
  its `SSet.Enhanced.coneCategory` declaration and full signature were read,
  together with its construction from `comma`, `constantDiagrams` and
  `diagramVertex`. A comma cone is not an object used by this node.
- Mathlib `CategoryTheory.Localization.Construction`:
  `MorphismProperty.Localization`, `MorphismProperty.Q`.
- Mathlib's simplicial cartesian structure, `BinaryFan`, `IsLimit.lift`,
  `ihom`, `ihom.ev`, and braiding are reused, not copied.
- Proof dependencies are imported non-publicly: `ExInfinityFiniteProducts`,
  `KanQuillenRightProper`, `ModelInfinityDerivedAdjunction`,
  `QuillenDerivedCounitCriterion`, `RigidificationEquivalenceDetection`,
  Mathlib `AnodyneExtensions.Inner.PushoutProduct`, and Mathlib
  `ModelCategory.FundamentalLemma`. The two other proof dependencies are
  already public statement imports. All eleven proof steps, including the
  fixed-cylinder comparison and the actual product/counit square, are carried
  in the theorem docstring. No proof import closes a cycle: none of these
  imported modules imports this new module.

Edge cases checked before writing:

- K empty: Fun(K,Q) is terminal, X×K is empty, and both Hom sets are singletons.
- X empty: its product and fixed cylinder are empty; evaluation and the
  unique-map clauses still have exactly the displayed types.
- Q empty: it is still a quasicategory; with K empty its function object is
  terminal, otherwise the allowed map sets have the appropriate empty cases.
- K = Δ[0]: the exponential and evaluation reduce to the usual identity
  representation; nothing in the statement excludes degree zero.
- Empty object sets in rigidification: the product is empty and the local DK
  condition is vacuous only in the mathematically appropriate case; essential
  surjectivity still comes from the actual product comparison.
- Nerves of categories with noninvertible arrows: they are allowed Q. The
  proof uses the invertible two-object groupoid interval, never Δ[1] as a
  categorical weak-equivalence cylinder.
- Arbitrarily large small objects: u is unrestricted, the ordinary
  localization lies in u+1, and the categorical-equivalence tests may enlarge
  to max u v. No object/morphism-universe equality is imposed on a site.

Searches executed for an exact existing statement:

- `msearch.py ... leanfinder`, query “The Joyal homotopy category is cartesian
  closed with simplicial internal hom and rigidification preserves products up
  to Dwyer Kan equivalence”: eight hits, including `hoFunctor` preservation of
  products and `SSet.instMonoidalClosed`. These concern the functor to ordinary
  categories or the unlocalized internal hom, and do not give this statement.
- `msearch.py ... loogle`, query `SSet, MonoidalClosed, Quasicategory`:
  zero hits, unknown identifier MonoidalClosed reported by the service.
- `msearch.py ... grep`, query
  `Joyal|rigidification|DwyerKan|IsCategoricalEquivalence`, subdirectory
  AlgebraicTopology: five hits, all for the unrelated abstract Joyal trick.
- `msearch.py ... leansearch`, query “The localization of simplicial sets at
  categorical equivalences has products and exponential objects given by
  simplicial mapping objects”: eight hits. `Localization.hasProductsOfShape`
  gives an abstract product-transfer API with a stability hypothesis;
  `Functor.IsLocalization.prod` localizes a product of categories.
  Neither supplies this Joyal stability/exponential/DK statement.
- `rg` on `WeilConjectures/` for Joyal, rigidification, homotopy-exponential and
  the exact node id: only unrelated Picard/Artin--Schreier rigidifications,
  no statement of this node. Exact node-id search has no upstream result.
- `rg` on `lean/Sheaf` finds the Joyal structure, its whole-functor testing
  theorem, and several coherent-nerve/rigidification constructions, all read
  to distinguish their signatures. None states localization products and
  evaluation exponentials plus the DK product comparison.
- Exact proposed names were searched in `dag/lean_names_upstream.json`,
  Mathlib, upstream and `lean/Sheaf`: no collision. The two helper names are
  small wrappers around existing constructions belonging to this item's
  canonical maps, as permitted by the missing-helper rule; they are listed
  in `lean.declarations` with source and blueprint docstrings.

I read HTT Corollaries the project server and the project server, Proposition the project server and the proof
of Proposition the project server, printed pp. 92--94, online at
https://www.math.ias.edu/~lurie/papers/HTT.pdf. They give the same product,
rigidification comparison and localization exponential, including arbitrary
K and fibrant Q. No statement correction or STATEMENT-DISPUTED issue was found.

Current worker audit (2026-10-17): checked the earlier attempt against the
current DAG. Only `lean` differs in the node copy. Fixed the stale worker-report
paragraph that still named `def-coef-complete-algebroid`: the actual third
statement dependency is `def-cbc-enhanced-diagrams-cones`. Added its direct
public import and read its recorded declaration and primitive conventions.
The theorem and helper formulas are unchanged. Updated `lean.date` to UTC today.
Repeated LeanFinder, Loogle, LeanSearch and Mathlib grep through `msearch.py`,
and direct upstream, side-library and name-collision searches. No exact existing
statement or declaration-name collision was found. Current wrapper validation
and the delivery dry run are recorded below after completion.

## Earlier second reading (a previous round; superseded)

The following reading is retained from the earlier attempt. The current worker
has corrected the dependency-report paragraph and added its direct import as
recorded above; the dispatcher's independent second reader must check these
changes before delivery.


I read the node statement, its source place (Lurie, HTT, Corollaries the project server and
the project server, Proposition the project server, and the proof of Proposition the project server, pp. 92--94),
and the declarations recorded for all three statement dependencies.

The statement's objects and hypotheses match the Lean signature as follows.

- The fixed universe convention is rendered by `universe u v`, `SSet.{u}`, and
  enlarged tests `SSet.{max u v}`. `D : CoherentNerveComparisonStatement.{u}` is
  the recorded coherent-nerve adjunction, and `M : ModelCategory SSet.{u}` with
  `hJoyal` gives exactly the recorded categorical-equivalence test for the weak
  equivalences of `M`.
- The ordinary localization at categorical equivalences is rendered by
  `M.categoryWithWeakEquivalences.weakEquivalences`, its `Localization` functor
  `Q`, and morphisms between `Q.obj` objects. No fibrancy, nonemptiness, or finite
  size hypothesis is added to `K`, `L`, `X`, or `Q`.
- The first conclusion clause, `∀ K L, Nonempty (IsLimit (localizedProductFan
  ... K L))`, states that the degreewise product with its two actual projections
  is the categorical product in the localization. The helper is exactly the fan
  made from `Q.map (fst K L)` and `Q.map (snd K L)`.
- The second clause, `∀ K L, ∃ c h, DwyerKanEquivalence (...)`, introduces a
  binary product cone `c` of `D.rigidification.obj K` and
  `D.rigidification.obj L`, requires `h : IsLimit c`, and applies `h.lift` to
  the two rigidified degreewise projections. Thus it is the specified natural
  functor `C[K × L] → C[K] × C[L]`, with the product target supplied by its
  universal property, rather than an arbitrary comparison map.
- The final clause quantifies `K` and a quasicategory `Q`, asserts that the
  existing simplicial internal hom `(ihom K).obj Q` is a quasicategory, and for
  every `X` and product-limit witness `h` asserts bijectivity of
  `localizedEvaluation`. Its formula first takes the unique localization-level
  pairing of `f : [X] → [Fun(K,Q)]` with `1_K`, then composes with the actual
  simplicial braiding and `ihom.ev`; hence its domain and codomain are precisely
  `[X, Fun(K,Q)]_J` and `[X × K, Q]_J` in the node's order.

Edge cases were checked: empty `K`, `L`, `X`, or `Q`; `K = Δ[0]`; empty object
sets in the rigidifications; and arbitrary non-fibrant `K,L` and arbitrary
quasicategory `Q`. The quantifiers and universes include all of these cases, and
no characteristic, size equality, nonemptiness, or fibrancy assumption is hidden.

I repeated the three required searches (LeanFinder, Loogle/LeanSearch, and grep)
in Mathlib, `WeilConjectures/`, and `lean/Sheaf`. The hits were the ordinary
simplicial internal hom, `hoFunctor`'s ordinary homotopy-category product
comparison, and Joyal's lifting trick; none states the Joyal localization
exponential together with the rigidification product DK equivalence. The exact
declaration names and node id also have no collision. The recorded dependency
declarations were opened and used; no private copy or second definition occurs.

No mismatch was found. The module and node copy therefore required no repair;
the node's `lean.statement` remains verbatim equal to the theorem signature. The
module has only the postponed theorem proof permitted at stage 2, with real-data
helpers `localizedProductFan` and `localizedEvaluation`, and its docstrings carry
the source and blueprint id. `scompile.py` compiled the file as both sandbox and
library compilation with no errors or warnings.

## Second reading by Q30

I read the node statement, its HTT source place (Corollaries the project server and the project server,
Proposition the project server, and the proof of Proposition the project server, pp. 92--94), and the
three statement-dependency declarations before checking the Lean signature.
The item-by-item rendering is:

- The fixed nested universes are `universe u v`, with `SSet.{u}` objects and
  `SSet.{max u v}` quasicategory tests in `hJoyal`; no equality of universes is
  imposed. `D : CoherentNerveComparisonStatement.{u}` is the recorded coherent
  nerve/rigidification interface, and `M` with `hJoyal` is the Joyal localization
  interface. Verdict: matches the node and dependencies.
- Ordinary localization is `M.categoryWithWeakEquivalences.weakEquivalences`,
  with objects `W.Q.obj X` and morphisms between them. Verdict: the stated
  localization and Hom sets are rendered exactly, with no fibrancy or size
  restrictions on `K`, `L`, `X`, or `Q`.
- The product clause is
  `forall K L, Nonempty (IsLimit (localizedProductFan W K L))`; the helper uses
  the actual degreewise projections `W.Q.map (fst K L)` and `W.Q.map (snd K L)`.
  Verdict: exact categorical-product clause and projections.
- The rigidification clause is
  `forall K L, exists c h, DwyerKanEquivalence (...)`, where `c` is a
  `BinaryFan` of the two rigidifications, `h : IsLimit c`, and `h.lift` is
  applied to the two actual rigidified product projections. Verdict: this is
  the specified natural map `C[K x L] -> C[K] x C[L]`, not an arbitrary
  replacement map.
- For every `K` and quasicategory `Q`, the conclusion asserts
  `((ihom K).obj Q).Quasicategory`; `ihom` is Mathlib's simplicial internal hom,
  whose simplices are maps from `K x Delta[n]`. Verdict: exact Fun construction
  and quasicategory clause.
- For every `X` and product-limit witness `h`, the final clause is
  `Function.Bijective (localizedEvaluation W X K Q h)`. Its helper first forms
  the unique localization-level pairing with `1_K`, then composes the actual
  braiding and `ihom.ev`, so its domain and codomain are precisely
  `[X,Fun(K,Q)]_J` and `[X x K,Q]_J` in the node's order. Verdict: exact
  evaluation-induced bijection and actual evaluation requirement.
- The concluding exponential sentence is represented by the preceding product,
  quasicategory, and bijectivity clauses; no ordinary homotopy-category
  exponential is substituted. Verdict: no clause is omitted or strengthened.

Edge cases checked against the source: empty `K`, `L`, `X`, or `Q`; `K = Delta[0]`;
empty rigidification object sets; arbitrary non-fibrant factors; degree zero; and
`u = 0` or `v = 0`. All are included by the quantifiers and no characteristic,
nonemptiness, finiteness, or universe restriction is hidden. The product and
evaluation helpers have real data and contain no `sorry`; the theorem has only
the permitted postponed proof.

I repeated the required searches with `msearch.py` (LeanFinder, Loogle and
LeanSearch), and `rg` over Mathlib, `WeilConjectures/`, the repository's
`lean/Sheaf`, DAG names, and the exact node id. The only hits were Mathlib's
ordinary simplicial `ihom`, `hoFunctor` product material, and unrelated
rigidification or Joyal constructions. No exact declaration or statement exists.
The dependency declarations `SSet.exists_joyal_model_structure`,
`CategoryTheory.CoherentNerveComparisonStatement`/`rigidification`, and
`SSet.Enhanced.coneCategory` were opened and match the uses; no private copy or
second definition was found.

No mismatch was found and no repair was needed. The node copy changes only its
`lean` record; `lean.statement` is verbatim the theorem signature. Compilation
with `scompile.py Q30 lem-coef-joyal-homotopy-exponentials
lean/Sheaf/AlgebraicTopology/JoyalHomotopyExponentials.lean` succeeded for both
the sandbox and library checks with no errors or warnings. No citer audit or
statement correction applies.
