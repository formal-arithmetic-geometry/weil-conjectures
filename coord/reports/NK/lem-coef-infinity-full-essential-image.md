## Worker report

The module `Sheaf.CategoryTheory.InfinityFullEssentialImage` states
`SSet.Enhanced.fullyFaithful_fullEssentialImage`, with its single proof `sorry`.
Its helper `SSet.Enhanced.fullEssentialImage` constructs the exact full subcomplex
specified in this node, using the already recorded full-subcomplex definition.
No arbitrary map or choice supplies its data. This is a helper for the owning
node's specified subcategory, not a second definition of enhanced categories,
full subcategories, functor equivalence, or a separate independent notion.

Hypothesis and clause correspondence:

- The universe convention is the explicit arbitrary `universe u` and
  `{X Y : SSet.{u}}`. This is a containing universe for both simplicial sets,
  as the node's proof explicitly permits; it imposes no original smallness
  assumption. Internal functor simplicial sets already exist in this universe.
- Infinity-categories X and Y are `[Quasicategory X] [Quasicategory Y]`.
- The coherent functor is the simplicial map `(J : X ⟶ Y)`.
- Full faithfulness is `(hJ : IsFullyFaithful J)`, the recorded predicate
  quantifying over every pair of vertices and asserting weak homotopy
  equivalence of the induced right-pinched mapping-space map.
- The object class defining Y₀ is exactly
  `∃ (x : X _⦋0⦌) (e : Y _⦋1⦌), Y.δ 1 e = y ∧
  Y.δ 0 e = J.app _ x ∧ IsEquivalenceEdge Y e`.
  The face equations orient the edge from y to Jx, and the dependency's
  `IsEquivalenceEdge` includes its inverse and both triangle witnesses.
- Y₀ is `(fullEssentialImage J).toSSet`. The recorded `fullSubcomplex` keeps
  exactly all simplices whose vertices satisfy this object predicate; there is
  no selection or loss of higher simplices.
- The restricted functor is
  `∃ J₀ : X ⟶ (fullEssentialImage J).toSSet, J₀ ≫
  (fullEssentialImage J).ι = J ∧ ...`. The equation specifies the restriction
  uniquely, since the inclusion is degreewise injective (hence monic).
  Expressing its existence together with the conclusion avoids constructing
  data using any postponed theorem.
- `IsFunctorEquivalence J₀` unfolds to a simplicial map K in the reverse
  direction, `AreNaturallyEquivalent (J₀ ≫ K) (𝟙 X)`, and
  `AreNaturallyEquivalent (K ≫ J₀) (𝟙 Y₀)`. In diagrammatic composition these
  are precisely KJ₀ ≃ 1_X and J₀K ≃ 1_Y₀. The natural equivalences are edges
  of the internal functor simplicial sets with inverse-triangle witnesses,
  so all coherence is retained.

Dependency declarations used, with their source and full interfaces read:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.fullSubcomplex`, `IsEquivalenceEdge`, `IsFullyFaithful`,
  `mappingSpace`, `mappingSpaceMap`, `AreNaturallyEquivalent`, and
  `IsFunctorEquivalence`. It imports Mathlib's `SSet` and `Quasicategory`.
- Proof-only imports from recorded proof dependencies:
  `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`
  (`SSet.Enhanced.enhanced_functor_cone_calculus`),
  `Sheaf.CategoryTheory.InfinityMappingComposition`
  (`SSet.Enhanced.mapping_composition`), and
  `Sheaf.CategoryTheory.SimplicialHomotopyEquivalenceWeak`
  (`SSet.Enhanced.simplicial_homotopy_equivalence_weak`).
- The remaining proof dependency `lem-coef-infinity-local-adjoint-criterion`
  is now recorded and imported from
  `Sheaf.CategoryTheory.InfinityLocalAdjointCriterion`
  (`SSet.Enhanced.infinity_local_adjoint_criterion`). Its full signature and
  docstring were read during this refresh. It supplies the simultaneous unit,
  counit, functor-space triangle simplices, and canonical mapping comparisons.
  It is a proof-only import; no definition data are chosen from it.

The source https://kerodon.net/tag/01JX was opened: Theorem the project server equates
functor equivalence with full faithfulness and essential surjectivity. Applying
it to the full replete essential image gives exactly this node's assertion.
The docstring follows all six proof steps of the node, including the coherent
local-adjoint construction rather than an unsupported assembly of objectwise
inverse choices.

Edge cases checked mathematically before writing:

- Empty X gives an empty vertex predicate and hence an empty full subcategory,
  even if Y is nonempty. The restriction and its inverse between empty
  simplicial sets exist; the natural-equivalence conditions remain valid.
- Empty Y forces empty X when J is given; no inhabitedness binder excludes it.
- Identity functors have the entire target as full essential image, since
  degenerate identity edges have the required two inverse triangles.
- A proper full essential image is permitted; J need not be essentially
  surjective onto Y itself. Objects merely equivalent to image vertices are
  included, with every higher simplex on such vertices.
- No completeness, presentability, colimits, choices of representatives, or
  full faithfulness on ordinary hom sets is assumed. Arbitrary containing
  universe u covers the node's size convention.

Searches made through `msearch.py NK lem-coef-infinity-full-essential-image`:

- LeanFinder: `fully faithful infinity functor full essential image coherent
  quasi inverse`. Eight hits; the nearest was ordinary-category
  `CategoryTheory.Equivalence.fullyFaithfulToEssImage`. Its source signature at
  `Mathlib/CategoryTheory/Equivalence.lean:711` was inspected: it takes
  `F : C ⥤ D`, `[F.Full]`, `[F.Faithful]`, and does not cover quasicategories.
- Loogle: `fullyFaithfulToEssImage, Functor.FullyFaithful`. No hits (the service
  reported an unknown unqualified identifier). Repeated with `"essImage"`:
  twelve hits, all ordinary-category essential-image interfaces, not this
  coherent simplicial theorem.
- LeanSearch: `A fully faithful functor of infinity categories is equivalent
  to its full essential image`. Eight hits, again ordinary-category full
  faithfulness and essential-image statements; no exact match.
- Mathlib grep: `fullyFaithfulToEssImage|full essential image` in
  `CategoryTheory`: one hit, the ordinary-category instance just inspected.
- Mathlib grep: `essentialImage|fullEssentialImage|fullyFaithful|IsFunctorEquivalence`
  in `AlgebraicTopology/Quasicategory`: no hits.
- `rg` of upstream `WeilConjectures` and shared `lean/Sheaf/CategoryTheory`
  for `essImage|essentialImage|fullEssential|toEssential|IsFullyFaithful|IsFunctorEquivalence`
  found ordinary essential-image APIs and existing enhanced predicates, but
  no theorem about this full replete essential image. The simplicial-enriched
  `SimplicialFullyFaithfulHomotopyImage` file concerns Bergner images, a
  different interface. `rg` of the exact item id in upstream found no match.
- `rg` of `dag/lean_names_upstream.json` for `essImage|fullEssentialImage`
  found no candidate. The chosen full declaration names do not occur in the
  upstream or shared source.

No statement correction, disputed statement, new independent definition node,
or dependency module was required. The item copy changes only `lean`.

Fresh validation: `scompile.py NK lem-coef-infinity-full-essential-image`
compiled the updated module in sandbox and library contexts in 1.2 s each,
with no errors or warnings. The required dry run is performed next.
All binders and universes are explicit and `autoImplicit` is disabled.

Current worker refresh (UTC 2026-10-16): reread the current node and its sole
statement dependency, checked that the sandbox differs only in `lean`, reopened
Kerodon Tag 01JX, and repeated LeanFinder, Loogle `"essImage"`, Mathlib
quasicategory grep, upstream/shared `rg`, exact-id search, and the upstream name
index search. No exact existing declaration was found. The now-recorded
local-adjoint proof dependency is imported; the statement and definition are
unchanged. The second reading below is retained from the prior attempt; a new
second reader will review this worker refresh before delivery.

## Earlier second reading (a previous round; superseded)

I read the item node, its Kerodon source place, the dependency declarations, and the
module independently. The node introduces fixed universes \(\mathcal U\in\mathcal U'\),
infinity-categories \(\mathcal X,\mathcal Y\) fitting in a containing universe, a coherent functor
\(J:\mathcal X\to\mathcal Y\), and full faithfulness. The Lean binders
`{X Y : SSet.{u}}`, `[Quasicategory X] [Quasicategory Y]`, `(J : X ⟶ Y)`, and
`(hJ : IsFullyFaithful J)` render these objects and hypotheses in the project’s
single arbitrary ambient universe; `SSet.{u}` makes each simplicial set \(u\)-small
and the internal mapping and functor simplicial sets remain in that ambient universe.
No completeness, presentability, or extra algebraic hypotheses are introduced.

The node defines \(\mathcal Y_0\) as the full subcategory on vertices \(y\) admitting
an \(x\) and an equivalence \(y\simeq Jx\). The helper
`SSet.Enhanced.fullEssentialImage` uses exactly
`∃ x e, Y.δ 1 e = y ∧ Y.δ 0 e = J.app _ x ∧ IsEquivalenceEdge Y e`, and
`fullSubcomplex` retains every simplex all of whose vertices satisfy this predicate.
Thus it is the full replete essential image, including higher simplices. The first
conclusion clause is rendered by
`∃ J₀ : X ⟶ (fullEssentialImage J).toSSet,
J₀ ≫ (fullEssentialImage J).ι = J`; this is precisely the restriction and its
factorization through the inclusion. The second clause is rendered by
`IsFunctorEquivalence J₀`, whose recorded definition supplies a reverse simplicial
map `K` and `AreNaturallyEquivalent` witnesses for `J₀ ≫ K ≃ 𝟙 X` and
`K ≫ J₀ ≃ 𝟙 Y₀`, exactly the node’s coherent quasi-inverse conclusion (with the
project’s composition order).

I checked the dependency signatures rather than names alone: `IsEquivalenceEdge`,
`fullSubcomplex`, `IsFullyFaithful`, `AreNaturallyEquivalent`, and
`IsFunctorEquivalence` are the declarations in
`Sheaf.CategoryTheory.EnhancedDiagramsCones`; the theorem imports the stated proof
modules `EnhancedFunctorConeCalculus`, `InfinityMappingComposition`, and
`SimplicialHomotopyEquivalenceWeak`. At that earlier reading the proof-only node
`lem-coef-infinity-local-adjoint-criterion` was not recorded; the current worker
refresh adds its now-recorded module as a proof-only import. No private
replacement was added.

Edge cases remain covered: empty \(X\) gives an empty image; a map into empty \(Y\)
forces empty \(X\); identity functors have the whole target as image; equivalent
but nonidentical target vertices are included; no inhabitedness, characteristic,
finite, or nonempty-index assumption is present; and `u` is arbitrary. I searched
Mathlib CategoryTheory and AlgebraicTopology/Quasicategory, upstream
`WeilConjectures/`, shared `lean/Sheaf/`, and the DAG name index using LeanFinder,
Loogle, LeanSearch, and `rg`/`msearch.py`. The only nearby match is the ordinary
category declaration `CategoryTheory.Equivalence.fullyFaithfulToEssImage`, which
uses hom-set full faithfulness and cannot express this quasicategorical statement;
no exact full-essential-image notion or theorem exists.

No mismatch was found and no Lean source was changed. The second reading records the declaration binding and this audit; no statement
correction, new node, or dependency repair is required. The module compiled
cleanly with `scompile.py` in sandbox and library contexts, with no errors or
unexpected warnings.


Independent second-reader search details (2026-10-17):

- LeanFinder, `quasicategory weak equivalences of mapping complexes equivalence to
  essential image`: eight hits, concerning model-category homotopy localization
  and `SSet.Truncated.HomotopyCategory.functorEquiv`; none is this theorem.
- Loogle, `"essentialImage"`: zero hits.
- LeanSearch, `Every quasicategory functor with equivalent mapping spaces admits an
  inverse onto its replete image`: eight ordinary-category/localization hits,
  including `fullyFaithfulToEssImage`, whose signature I read at
  `Mathlib/CategoryTheory/Equivalence.lean:711`. Its arguments are an ordinary
  functor and `Full`/`Faithful` instances, so it does not apply here.
- Independent `rg -i` with `essential.image|essImage|Dwyer.Kan|categorical.equivalence`
  on upstream `WeilConjectures`, Mathlib's quasicategory subtree and Equivalence
  module, and shared `lean/Sheaf/CategoryTheory` found no exact match. I read the
  potentially nearby `SimplicialFullyFaithfulHomotopyImage` module: its objects
  are simplicial categories and its conclusion is an injection of localized Hom
  sets with an essential-image test; its proof explicitly uses the present node.
  It cannot replace this theorem. The shared DAG name index supplies no matching
  quasicategorical full-essential-image construction.

I opened https://kerodon.net/tag/01JX independently: Theorem the project server assumes only a
functor of infinity-categories and equates equivalence with full faithfulness plus
essential surjectivity. No finiteness or nonemptiness assumption is hidden in the
source. The full essential-image restriction is essentially surjective by its
vertex predicate; the node's six-step proof and the theorem's docstring supply the
coherent inverse. The distinction between the small universe and containing
universe introduces no extra object in this statement: take `u` to be the
containing level of the simplicial models as permitted by node proof step 1.
The original categories need not be small in the originally designated smaller
universe. No unbound universe or variable, `let`/`show` statement binder, hollow
definition, or proved theorem appears in the delivered module.

## Second reading by NK

I reread the node statement, its six proof steps, the dependency declaration
`def-cbc-enhanced-diagrams-cones`, and the source at Kerodon Tag 01JX. The statement
items and their Lean renderings are (verdict: exact for each item):

1. The universe convention is “small” U-small categories in a containing U-prime
   universe. Lean uses the universe-polymorphic `{X Y : SSet.{u}}`; an arbitrary
   `u` can be chosen as the containing level, so this introduces no finiteness or
   universe equality hypothesis.
2. The objects are infinity-categories X and Y, rendered by `{X Y : SSet.{u}}`
   with `[Quasicategory X] [Quasicategory Y]`.
3. The coherent functor is `(J : X ⟶ Y)`.
4. Full faithfulness is `(hJ : IsFullyFaithful J)`, whose dependency definition is
   `forall x y, IsWeakHomotopyEquivalence (mappingSpaceMap J x y)`, exactly the
   node's mapping-space equivalences.
5. The full replete essential image is the helper
   `fullEssentialImage J := fullSubcomplex Y (fun y => exists x e, Y.δ 1 e = y and
   Y.δ 0 e = J.app _ x and IsEquivalenceEdge Y e)`. In the right-pinched convention
   `δ 1` is the source and `δ 0` the target, so this is an equivalence edge
   `y -> Jx`, equivalent to the node's `y ≃ Jx`; `fullSubcomplex` keeps every
   simplex whose vertices satisfy the predicate.
6. The restricted functor and its factorization are
   `exists J₀ : X ⟶ (fullEssentialImage J).toSSet,
   J₀ ≫ (fullEssentialImage J).ι = J`.
   This is the required `J₀ : X -> Y₀`; the inclusion equation pins the restriction.
7. The coherent quasi-inverse conclusion is `IsFunctorEquivalence J₀`. The recorded
   dependency expands this to a reverse map `K`, `AreNaturallyEquivalent (J₀ ≫ K)`
   `(𝟙 X)`, and `AreNaturallyEquivalent (K ≫ J₀) (𝟙 Y₀)`, with the same composition
   order as `KJ₀ ≃ 1_X` and `J₀K ≃ 1_{Y₀}`.

The source theorem states precisely equivalence iff full faithfulness plus essential
surjectivity for a functor of infinity-categories; it adds no completeness,
presentability, characteristic, or nonemptiness assumptions. The Lean module has one
real helper definition and one postponed theorem, with source and blueprint
docstrings; `autoImplicit` is false and no hollow data or private replacement is
used. The proof-only imports match the node's proof dependencies, including the
recorded `InfinityLocalAdjointCriterion` interface.

Edge cases checked: `X = ∅` gives the empty image and an empty restriction; an empty
`Y` forces an empty `X` when `J` exists; `J = 𝟙` gives the whole target image;
equivalent but distinct target vertices are included; empty mapping spaces and all
dimensions, including degree zero, remain allowed; and every universe level `u` is
allowed. There is no index, characteristic, finiteness, or inhabitedness binder.

I reran the independent searches. `msearch.py` LeanFinder returned only ordinary
category results, chiefly `CategoryTheory.Equivalence.fullyFaithfulToEssImage`;
Loogle returned no `essentialImage` result; the exact-name grep returned no match.
I also searched Mathlib's quasicategory tree, upstream `WeilConjectures`, shared
`lean/Sheaf/CategoryTheory`, and `dag/lean_names_upstream.json`. The nearby
`SimplicialFullyFaithfulHomotopyImage` concerns simplicial categories and localized
hom sets and cannot replace this quasicategorical result. No existing declaration or
duplicate notion was found.

No mismatch was found. I changed no Lean declarations or node statement. The sandbox
module compiled with `scompile.py` (both sandbox and library passes), with no errors
or warnings; all variables and universes are explicit. No statement correction,
dependency repair, or new definition node is required.

Additional independent search: LeanFinder for “A simplicial map with equivalences on
right mapping complexes has an inverse on the replete subcomplex generated by its
vertices” returned eight subcomplex/paired-cell results, including
`SSet.Subcomplex.lift` and `topIso_inv_app_coe`, not this theorem. The accompanying
`rg` search for `replete|inverse.*subcomplex|subcomplex.*inverse|mapping.*complex.*equivalen`
in Mathlib quasicategories, upstream and shared CategoryTheory found only different
ordinary repleteness results and consumers of this node. Verdict remains no match.
