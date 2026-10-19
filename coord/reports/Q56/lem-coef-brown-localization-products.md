## Worker report

The module `Sheaf.CategoryTheory.BrownLocalizationProducts` defines the canonical map
`SSet.Enhanced.brownProductLocalizationMap` and states
`SSet.Enhanced.brown_localization_products`. The latter is the only postponed theorem,
with proof `sorry`. The helper has actual simplicial-map data and no postponed proofs.
No statement correction, disputed statement, new node, or dependency repair is needed.

Source checked online: Cisinski, *Higher Categories and Homotopical Algebra*,
https://cisinski.app.uni-regensburg.de/CatLR.pdf, Proposition 7.7.1, printed p. 396
(PDF page 411), and Definition 7.4.12, printed pp. 365--366. Proposition 7.7.1 treats
an arbitrary set of categories with weak equivalences and fibrations; taking opposites
gives precisely the all-cofibrant ordinary-category case here. Its proof uses exactness,
conservativity, fractions and approximation, as expanded in the node and theorem docstring.
The source does not require finite J or coproducts in the individual categories.

Hypotheses and conclusions, clause by clause:

| Node clause | Lean rendering |
| --- | --- |
| Any small set J | `(J : Type w)`, with no `Finite`, `Fintype`, or `Nonempty` binder |
| Ordinary categories A_j | `(A : J → Type u) [∀ j : J, Category.{v} (A j)]` |
| Chosen initial object 0_j | `(zero : ∀ j : J, A j)` and `(hzero : ∀ j : J, CategoryTheory.Limits.IsInitial (zero j))` |
| Classes C_j and W_j | `(C W : ∀ j : J, MorphismProperty (A j))` |
| Each class contains all isomorphisms | `hCiso` and `hWiso`, the inclusions `MorphismProperty.isomorphisms (A j) ≤ C j` and `≤ W j` |
| C_j is closed under composition | `[∀ j : J, (C j).IsStableUnderComposition]` |
| W_j is closed under composition and satisfies two-out-of-three | `[∀ j : J, (W j).HasTwoOutOfThreeProperty]`; this Mathlib class extends `IsStableUnderComposition`, `HasOfPostcompProperty W`, and `HasOfPrecompProperty W` |
| W_j is retract closed | `[∀ j : J, (W j).IsStableUnderRetracts]` |
| Every initial map is in C_j | `hcof : ∀ (j : J) (X : A j), C j ((hzero j).to X)` |
| Every arrow factors as C_j then W_j | `[∀ j : J, MorphismProperty.HasFactorization (C j) (W j)]`; this requires only existence of individual factorizations |
| Cofibration pushouts exist | `hpush`, for every `i : X ⟶ Y`, `f : X ⟶ Z`, gives `C j i → HasPushout i f` |
| Such pushouts remain cofibrations | `[∀ j : J, (C j).IsStableUnderCobaseChange]`, testing arbitrary pushout squares |
| Pushouts of C_j intersect W_j remain in that intersection | `[∀ j : J, (C j ⊓ W j).IsStableUnderCobaseChange]`; their existence already follows from `hpush` |
| Given maps q_j from enlarged nerves to L_j | `(L : J → SSet.{max u v w t})` and `q : ∀ j, largeNerve.{u, v, max w t} (A j) ⟶ L j` |
| Each L_j is a quasicategory and q_j has the entire-functor-category localization property | `hq : ∀ j, IsLocalization (W j) (q j)`; the existing definition includes `Quasicategory`, inversion, and coherent equivalence of the full functor simplicial sets |
| Ordinary product category and coordinatewise weak equivalences | `∀ j : J, A j`, with Mathlib's Pi category instance, and `MorphismProperty.pi W` |
| The specified product map | `brownProductLocalizationMap A L q`, using `Pi.lift` of `q j` after the degreewise nerve of `CategoryTheory.Pi.eval A j` |
| Nerve/product identification | The j-coordinate sends a lifted simplex `s` to `q j` applied to `ULift.up (s.down ⋙ CategoryTheory.Pi.eval A j)`. This is restriction of the functor `[n] → ∏ A_j` to its j-coordinate, so exactly the displayed map in every degree |
| Target product is a quasicategory and the product map is a localization | The conclusion `IsLocalization (MorphismProperty.pi W) (brownProductLocalizationMap A L q)` |
| Same universal property on entire coherent functor categories | Unfolding the conclusion's existing `IsLocalization` quantifies over every ambient quasicategory T and gives an equivalence `Fun(product L_j,T) → Fun_W(N(product A_j),T)` whose composite with the full-subcategory inclusion is actual precomposition |
| Empty product included | `J` is arbitrary; no inhabitant is used by the definition or required by the theorem |
| No coproducts, model structures or finiteness assumed | No such binders occur; the localization definition is reused from its owning definition node, without invoking the finite-Reedy theorem |

Dependencies used:

- `def-cbc-enhanced-diagrams-cones`: public import
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`. Its existing
  `SSet.Enhanced.IsEquivalenceEdge`, `fullSubcomplex`, `AreNaturallyEquivalent`, and
  `IsFunctorEquivalence` are used through the coherent-localization interface.
  The source of the recorded `coneCategory` and all helper definitions was read.
- Added the already-landed definition node `def-coef-coherent-localization-interface`
  to `stmt_deps`, under brief-stage2 §5's permission to cite landed notions.
  Public import `Sheaf.CategoryTheory.FiniteReedyLocalization` supplies exactly its
  recorded `HomotopicalAlgebra.FiniteReedy.largeNerve`, `Inverts`, `localDiagrams`,
  and `IsLocalization`. Full signatures and docstrings were read. The fixed enlarged
  universe agrees with the definition node and the item's explicit size convention.
  This uses definitions only and adds no theorem dependency on finite Reedy localization.
- Mathlib: `CategoryTheory.Pi.eval`, the category instance on a dependent function type,
  `CategoryTheory.MorphismProperty.pi`, `CategoryTheory.Limits.Pi.lift`, `IsInitial`,
  `HasPushout`, and the standard morphism-property classes. The product of simplicial
  sets is the ordinary categorical product, computed degreewise in the presheaf category.
- Proof-only imports: `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`, with
  `SSet.Enhanced.enhanced_functor_cone_calculus`, and
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`, with
  `SSet.KanQuillen.right_proper_kan_quillen`. The other four named proof inputs have
  no recorded Lean modules at preparation time, so their imports are left to the
  maintainer when they are stated: `lem-coef-brown-fibrant-localization-pullbacks`,
  `lem-coef-brown-right-exact-extension`, `lem-coef-brown-left-fractions`, and
  `lem-coef-finite-colimit-approximation`. They are not statement prerequisites.

Edge cases checked before writing:

- Empty J: the ordinary product category is terminal, and both its nerve and the
  target simplicial product are terminal. `Pi.lift` takes the empty family, so the map
  is the unique terminal comparison. All factor hypotheses quantify over the empty set.
- Singleton J: the formula is q_j under the canonical singleton-product isomorphisms.
- Infinite J: no finite hypothesis or induction is built into the definition. The
  theorem is the Brown result, unlike ordinary finite-product localization in Mathlib.
- Terminal factor categories and the zero/initial objects: their initial maps and
  identities are retained; there is no nonzero or nontrivial hypothesis.
- Non-saturated W: neither source nor Lean assumes saturation. The proof docstring
  retains the two successive localized-retraction witnesses needed for conservativity.
- Independent universes: objects u, morphisms v, index w, and enlargement t are
  explicitly bound. The product category has object universe `max w u` and morphism
  universe `max w v`; both sides of its localization live in `max u v w t`.
  Arbitrarily large choices can be accommodated by enlarging these universe parameters.
- The helper uses actual coordinate projection functors and the universal product map;
  it neither quantifies over an arbitrary replacement map nor chooses localization data.

Searches for reuse:

- `msearch.py ... leanfinder "Arbitrary small products of Brown cofibration categories
  give products of infinity localizations"`: eight hits. The closest is
  `CategoryTheory.Functor.IsLocalization.pi`, which has `[Finite J]` and ordinary
  categorical localization. The other hits concern finite products or product stability
  of model-category fibrations, so none states this node.
- `msearch.py ... loogle "CategoryTheory.Functor.IsLocalization.pi"`: one hit, that same
  finite ordinary localization result. Its source signature was read in
  `Mathlib/CategoryTheory/Localization/Pi.lean`.
- `msearch.py ... grep "locali[sz].*pi|pi.*locali[sz]|product.*locali[sz]"
  CategoryTheory/Localization`: eleven hits in ordinary localization Prod, Pi,
  FiniteProducts, Equivalence and CalculusOfFractions; no coherent Brown product result.
- `msearch.py ... leansearch "Products of infinity localizations of categories of
  cofibrant objects"`: eight hits, again ordinary product localization and cofibrant
  objects; no match.
- `rg` in the upstream `WeilConjectures` tree for localization/product and Brown
  expressions, and `grep -rn "lem-coef-brown-localization-products"` there, found no
  declaration of this node. The latter returned no hits.
- `rg` in `lean/Sheaf` found the exact coherent-localization helpers in
  `FiniteReedyLocalization.lean` and the consumer
  `CocompleteCofibrationLocalization.lean`; the consumer refers to this theorem in
  its proof plan but does not state it. `rg` in `dag/lean_names_upstream.json`,
  `lean/Sheaf` and upstream found neither of the two new declaration names.

Validation: `scompile.py Q56 lem-coef-brown-localization-products` on the delivered
module passed its sandbox compile (2.6 s) and library-path compile (1.8 s), without
errors or warnings. No direct compiler or global build was run. The node copy changes
only `lean` and the addition of the landed definition node to `stmt_deps`.

## Second reading by Q56

I independently read the base node, the sandbox node and Lean file, both statement
 dependency records, and the implementations of their relevant declarations. There
is no repair note for this item. The source is not a Stacks tag: I opened Cisinski's
*Higher Categories and Homotopical Algebra*, Proposition 7.7.1 (printed p. 396,
PDF page 411), Definition 7.4.12 (printed pp. 365--366), and the preceding fibration
convention 7.4.6. The all-cofibrant ordinary case, after taking opposites, has the
pushout and factorization directions used here. Proposition 7.7.1 permits any set
of factors. It imposes neither coproducts in each factor nor a model structure.
The node explicitly assumes isomorphism containment and retract closure; the Lean
retains them. The fact that the cited source also treats more general categories
is not an additional restriction on this node's ordinary all-cofibrant case.

My object/hypothesis/conclusion inventory and its Lean match follows. Every row
has verdict **exact**.

| Node item | Lean rendering and check |
| --- | --- |
| Any small indexing set J | `J : Type w`; no finiteness or nonemptiness instance. |
| Ordinary factor categories | `A : J → Type u`, `[∀ j : J, Category.{v} (A j)]`. |
| Initial objects | `zero : ∀ j, A j`, `hzero : ∀ j, CategoryTheory.Limits.IsInitial (zero j)`; these are initial, not zero objects. |
| Two arrow classes in each factor | `C W : ∀ j : J, MorphismProperty (A j)`. |
| Both classes contain isomorphisms | `hCiso` and `hWiso`, inclusions from `MorphismProperty.isomorphisms (A j)`. |
| Composition closure of C and W | `C j` has `IsStableUnderComposition`; `W j` has `HasTwoOutOfThreeProperty`, whose source explicitly extends composition closure. |
| Two-out-of-three for W | The same `HasTwoOutOfThreeProperty` extends both cancellation properties for composable arrows. |
| Retract closure of W | `[∀ j, (W j).IsStableUnderRetracts]`. |
| All objects cofibrant | `hcof : ∀ j X, C j ((hzero j).to X)` uses the unique initial arrow. |
| Each arrow factors as C then W | `[∀ j, MorphismProperty.HasFactorization (C j) (W j)]`; its source asks for `Nonempty` factorization data for each map, without functoriality. |
| Pushouts of C exist | `hpush` quantifies over every span `i : X ⟶ Y`, `f : X ⟶ Z`, with `C j i → HasPushout i f`. |
| Those pushouts lie in C | `(C j).IsStableUnderCobaseChange`, whose source tests every pushout square and its new leg. |
| Pushouts of C intersect W stay in the intersection | `(C j ⊓ W j).IsStableUnderCobaseChange`; existence follows from `hpush` applied to the C component. |
| Specified quasicategories and localization maps | `L : J → SSet.{max u v w t}`, `q : ∀ j, largeNerve (A j) ⟶ L j`, `hq : ∀ j, IsLocalization (W j) (q j)`. |
| Whole coherent functor universal property of each q | The dependency's `IsLocalization` is quasicategoricity, `Inverts`, and an equivalence onto the full `localDiagrams` simplicial subset for every ambient quasicategory T; its composite with inclusion equals `(MonoidalClosed.pre q).app T`. |
| Ordinary product category | `∀ j : J, A j` with Mathlib's dependent Pi category; its arrows and composition are coordinatewise. |
| Coordinatewise weak equivalences | `MorphismProperty.pi W`, whose source is `fun _ _ f ↦ ∀ j, W j (f j)`. |
| Displayed product map with nerve/product identification | `brownProductLocalizationMap A L q`: `Pi.lift` of the projection nerve map followed by `q j`. At a simplex s its j-coordinate is `q j` applied to `ULift.up (s.down ⋙ CategoryTheory.Pi.eval A j)`. |
| Product is a quasicategory and displayed map is localization | Conclusion `IsLocalization.{max w u, max w v, t} (MorphismProperty.pi W) (brownProductLocalizationMap A L q)` includes both clauses. |
| Entire-functor-category conclusion, with specified restriction | Unfolding that same `IsLocalization` gives the equivalence onto `localDiagrams` and equality with actual precomposition by this product map, including higher simplices. |
| Empty product and absence of extra hypotheses | Neither declaration uses an index inhabitant; there is no coproduct, model-category, saturation, finite-index, or functorial-factorization assumption. |

Dependency audit: I read `FiniteReedyLocalization.lean` through the definitions
`largeNerve`, `Inverts`, `localDiagrams`, and `IsLocalization`; they are the exact
recorded interface of `def-coef-coherent-localization-interface`. In particular
`localDiagrams` uses the existing `fullSubcomplex`, not a core, and
`IsFunctorEquivalence` in `EnhancedDiagramsCones.lean` asks for a quasi-inverse with
coherent inverse equivalences. I opened that file's equivalence-edge and full-subset
constructions and the signatures of `AreNaturallyEquivalent` and
`IsFunctorEquivalence`. These realize the enhanced notions in the other statement
dependency. No private substitute or finite-Reedy theorem is used. Adding this
already-landed interface node to `stmt_deps` is authorized by brief-stage2 §5.
There are no new definition nodes or dependency modules to review, and no
`statement_change` or changed source statement requiring a citer audit.

Edge cases: empty J is allowed by all binders and by `Pi.lift`; the ordinary
product and simplicial product are terminal, so their canonical comparison is a
localization. Singleton and arbitrary infinite J use the same degreewise formula.
A terminal category and an initial object that is also zero are allowed; there is
no nontriviality requirement. An empty factor cannot have the initial object
already required by the node. No scheme, coefficient ring, characteristic, or
integer parameter occurs, so empty schemes, characteristic and n = 0 add no
cases. At simplicial degree zero the same projection formula applies to objects.
Object universe u, morphism universe v, index universe w and enlargement t are
independent. The product category has object universe `max w u` and morphism
universe `max w v`; its nerve and the target product lie in `max u v w t`.
This is exactly the node's common enlarged-universe convention, with no equality
of independent input universes imposed.

Independent reuse searches (all via the prescribed tools or read-only `rg`):

- LeanFinder: "The infinity localization of an infinite product of cofibration
  categories is the product of the localizations"; eight hits, led by
  `CategoryTheory.Functor.IsLocalization.pi`. I read its source in
  `Mathlib/CategoryTheory/Localization/Pi.lean`: it assumes `[Finite J]` and uses
  ordinary categorical localizations, so it does not state this node.
- Loogle: `CategoryTheory.Functor.IsLocalization.pi`; the same candidate and the
  same reason for rejection.
- LeanSearch: "Localization functor from a product of relative categories into a
  product of quasicategories"; eight ordinary localization hits (Pi, Prod,
  Bifunctor, finite-product preservation), none with this coherent universal property.
- Mathlib grep via msearch: `cofibrant.*localization|localization.*cofibrant|
  localization.*product|product.*localization` in `CategoryTheory/Localization`;
  ordinary product/localization material only.
- Read-only `rg` on upstream `WeilConjectures` for Brown, coherent localization,
  and localization/product combinations found ordinary Brown representability,
  ring localizations and algebraic tensor products, not this statement.
- Read-only `rg` on project `lean/Sheaf/CategoryTheory` and the upstream-name index
  found `CocompleteCofibrationLocalization.lean` referring to this node only in its
  proof plan; no matching theorem or collision with the two delivered names.

No mathematical or implementation mismatch was found. I left the Lean and node
unchanged and appended this independent reading. The helper has actual coordinate
map data; its `rfl` field checks simplicial naturality, not a postponed theorem.
The only theorem proof is `sorry`. Both declaration docstrings give the source
and blueprint id, and the theorem's seven numbered steps match all seven DAG proof
steps. Public imports serve the statement; the two non-public imports are the
currently recorded proof modules. All universes and variables are explicitly bound.
I checked verbatim equality of `lean.statement` with the theorem signature and
that every Lean source line is at most 100 characters.

Second-reader validation: the required `scompile.py Q56
lem-coef-brown-localization-products lean/Sheaf/CategoryTheory/BrownLocalizationProducts.lean`
passed both the sandbox compile (1.5 s) and library-path compile (1.7 s), with no
errors or warnings. No direct compiler, global build or live-file edit was used.
