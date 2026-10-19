## Worker report

The item is stated by `CategoryTheory.accessible_pie_closure` in
`Sheaf.CategoryTheory.AccessiblePieClosure`. Its three conjuncts are exactly the
small-product, inserter, and equifier assertions, including accessibility of each
specified projection. Its only postponed proof is `:= by sorry`. The entire
12-step proof now recorded in the shared node is transcribed into its docstring.
The node's statement is unchanged; `stmt_deps` gains only `def-coef-inserter`.

The missing independent notion is supplied in `Sheaf.CategoryTheory.Inserter`,
owned by the new node `def-coef-inserter`. It contains the actual object data,
compatible-arrow data, category operations and projection functor. There is no
choice of an unspecified category or arrow and no postponed data. The category's
proof fields are discharged directly from the source category laws and functor
laws; no additional theorem is claimed or proved.

Hypothesis and clause correspondence:

- The universe `mathcal U` is Lean universe `w`. Every ambient category has
  `Category.{w}`; `S : Type w` is precisely a small product index. The object
  universes `u₁` and `u₂` are independent of `w` and of each other. In particular
  there is no restriction that the object collections be small, or that the two
  categories have the same object universe. The inserter itself has object
  universe `max u₁ w`, with Hom universe `w`.
- Infinite regular cardinals are Mathlib's `Cardinal.{w}` with
  `Fact κ.IsRegular`. `Cardinal.IsRegular` includes `aleph0_le`; it is not a
  convention admitting finite cardinals. Its cofinality formulation is
  equivalent to the node's union formulation.
- The node's definition of a κ-filtered category is
  `CategoryTheory.IsCardinalFiltered`: every functor with fewer than κ arrows
  admits a cocone (`HasCardinalLT (Arrow A) κ`). This also enforces nonemptiness.
- κ-presentability is Mathlib's `IsCardinalPresentable`, meaning preservation by
  the covariant Hom functor. `IsAccessibleCategory.{w}` existentially chooses an
  infinite regular κ, and `IsCardinalAccessibleCategory` extends both
  `HasCardinalFilteredColimits` and `HasCardinalFilteredGenerator`. The latter
  supplies an essentially small object property of κ-presentables whose
  κ-filtered presentations have indexing category in `Type w`. Choosing
  representatives is equivalent to the node's small family formulation.
- Each factor is assumed accessible by
  `[∀ s, IsAccessibleCategory.{w} (A s)]`. No common cardinal is assumed. The
  first conjunct concludes `IsAccessibleCategory.{w} (∀ s, A s)` and
  `∀ s, (Pi.eval A s).IsAccessible.{w}`. Mathlib's `pi` category has tuples as
  objects, componentwise arrows and composition, and `Pi.eval` is its projection.
- In the second and third conjuncts, `F G : A ⥤ B` binds the two parallel
  functors; `[IsAccessibleCategory.{w} A]` and the corresponding class for `B`
  bind accessibility of their source and target. `[F.IsAccessible.{w}]` and
  `[G.IsAccessible.{w}]` bind their accessibility.
- Mathlib's `Functor.IsAccessible` directly says that some infinite regular
  λ is a preservation rank; it does not build source-colimit existence into
  this predicate. In the present statement the source is always accessible.
  If κ is its accessibility rank and λ a preservation rank, enlarge to the
  maximum of κ and λ, which is regular. Any diagram filtered at this maximum
  is filtered at each smaller rank. The source therefore has the required
  colimit and the functor preserves it. Thus the predicate is equivalent here
  to the node's definition, including its existence clause. The same argument
  applies to each projection, whose source accessibility is the paired clause.
- The inserter's objects are `Inserter F G`, with `obj : A` and
  `hom : F.obj obj ⟶ G.obj obj`. Its arrows are `Inserter.Hom X Y`, consisting
  of `hom : X.obj ⟶ Y.obj` and
  `F.map hom ≫ Y.hom = X.hom ≫ G.map hom`. Since Lean writes composition in
  diagrammatic order, this is precisely the symmetric form of
  `G(f) ∘ u = v ∘ F(f)`. Identities and composition are the corresponding
  operations in `A`. `Inserter.forget F G` sends `(X,u)` to `X` and an arrow
  to its underlying arrow. The second conjunct asserts accessibility of this
  category and this exact functor.
- In the third conjunct `α β : F ⟶ G` are natural transformations, so their
  naturality is part of their type. The equifier is the existing Mathlib full
  subcategory `ObjectProperty.FullSubcategory (fun X : A ↦ α.app X = β.app X)`.
  Its morphisms are all ambient morphisms between its objects. The functor
  `ObjectProperty.ι` for that same property is its inclusion. The conclusion
  asserts both its accessibility and the accessibility of the inclusion.
- Every accessibility conclusion independently quantifies its own cardinal.
  The theorem asserts no fixed common accessibility cardinal, preservation of
  all colimits, completeness, or any other extra conclusion.

Dependency declarations and source signatures read:

- `def-weil-pbc-category-colimit` is the Mathlib leaf recorded as
  `CategoryTheory.Limits.colimit`, in
  `Mathlib.CategoryTheory.Limits.HasLimits`. Its chosen cocone, `Cocone`,
  `IsColimit` and `colimit.desc` have the universal property used by the
  accessibility predicates. The module is explicitly imported publicly.
- `def-coef-inserter`: `CategoryTheory.Inserter`, `Inserter.Hom`,
  `Inserter.category`, `Inserter.forget`, from `Sheaf.CategoryTheory.Inserter`.
- The new node cites `def-nagata-category`, whose exact Mathlib match is
  `CategoryTheory.Category`, in `Mathlib.CategoryTheory.Category.Basic`.
  Its full signature and `CategoryStruct` data were read. The module is
  explicitly publicly imported by the new definition module.
- Accessibility definitions were read in
  `Mathlib.CategoryTheory.Presentable.LocallyPresentable`,
  `Mathlib.CategoryTheory.Presentable.Basic`,
  `Mathlib.CategoryTheory.Presentable.IsCardinalFiltered`, and
  `Mathlib.CategoryTheory.Presentable.CardinalFilteredPresentation`.
  The product and full-subcategory declarations were read in
  `Mathlib.CategoryTheory.Pi.Basic` and
  `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`.
- For proof dependencies already stated as Mathlib leaves, plain imports of
  `Mathlib.CategoryTheory.Presentable.Limits` and
  `Mathlib.CategoryTheory.Presentable.Dense` make available
  `Functor.isCardinalAccessible_of_isLimit`,
  `isCardinalPresentable_of_isColimit`, and the dense/filtered canonical
  presentable-object diagrams. Their full signatures were read. The proof-only
  node `lem-coef-accessible-system-ranks` currently has no Lean declaration or
  Mathlib match, so there is no module for it to import. The theorem's statement
  does not use its conclusion as data or as a hypothesis.

Source verification: I read the current blueprint ancestor's proof paragraph 2
and [Ching--Riehl, Appendix A, printed pp. 9--11](https://math.jhu.edu/~eriehl/coalgebraic.pdf).
The paragraph before Definition A.3 states that accessible categories and
accessible functors admit PIE limits created in categories. Definition A.3
specifies the inserter objects and commuting-square morphisms and the full
subcategory defining the equifier. The proof of Proposition A.1 explicitly
includes accessibility of the inserter and equifier projections. Small products
are the small product PIE case stated by the node. Remark A.4 confirms that an
output cardinal need not be the original cardinal. No source-based statement
correction is needed.

Edge cases checked before finalizing the statement:

- No factors: there is no `Nonempty S` hypothesis. The product is the terminal
  category and the projection clause is vacuous.
- An empty factor gives an empty product category; an empty generating family
  witnesses accessibility, and no nonempty-filtered diagram into it exists.
- Empty source categories give empty inserters and equifiers, which are allowed.
- `F = G` does not turn the inserter into a full subcategory: it still remembers
  an arbitrary endomorphism of each image. The new object and arrow data retain
  that distinction. For identity functors this is the category of objects with
  an endomorphism and commuting arrows.
- `α = β` includes every object; the full subcategory and inclusion are the
  expected whole-category presentation. An equifier with no satisfying objects
  is permitted. No equality of transformations is assumed globally.
- κ = ℵ₀ is allowed; no uncountability is added. Zero objects, initial or terminal
  objects, limits, cocompleteness and faithfulness are never hypotheses.

Searches made for reuse (before adding the missing definition):

- `msearch.py leanfinder`, query "Accessible categories are closed under small
  products inserters and equifiers with accessible projection functors": eight
  hits, consisting of accessibility definitions and standard consequences;
  none states PIE closure. In particular `IsAccessibleCategory` and
  `Functor.IsAccessible` are reused rather than redefined.
- `msearch.py loogle`, query `"IsAccessible", "Inserter"`: zero hits.
- `msearch.py leansearch`, query "The inserter category of two parallel functors
  has objects X with an arrow F X to G X and compatible morphisms": eight hits
  about `WalkingParallelPair`, `parallelPair`, and
  `IndParallelPairPresentation`; these are diagram-index or presentation
  constructions, not a category of inserter objects.
- `msearch.py leanfinder`, query "Definition of the inserter category of two
  parallel functors and its forgetful projection": eight hits about
  `parallelPair` and `IndParallelPairPresentation`, no inserter construction.
- `msearch.py grep`, query `Inserter|Equifier|inserter|equifier`, Mathlib
  subdirectory `CategoryTheory`: zero hits. Direct `rg` of Mathlib confirmed
  no such construction; the endofunctor-algebra category only covers its
  specialized source=target case and is not a generic parallel-functor inserter.
- Direct `rg -n -i 'inserter|equifier'` in the upstream `WeilConjectures` sources:
  no hits. Searching the item id there also returns no hits.
- The same direct search in the shared `lean/Sheaf` finds explanatory uses in
  `AccessibleMonadPresentability.lean` and
  `AccessibleCompletenessCharacterization.lean`, without definitions or a
  closure theorem. Declaration-name searches in `dag/lean_names_upstream.json`
  find no proposed-name collision.
- The DAG search finds this item and downstream explanatory uses, but no
  definition node for an inserter. `tools/blueprint_refs.py search inserter`
  and `search equifier` both return zero blueprint-node matches. Its
  `ancestor` command gives `prop-coef-integral-exceptional-adjoint`.
  The new node records the exact new-definition search outputs, including
  repository searches, in `mathlib_searches`.

There is no STATEMENT-DISPUTED claim or unresolved statement fault. All bound
universes and variables are explicit. Both delivered modules were compiled
separately, in dependency order, using the required `scompile.py` wrapper;
there were no errors or warnings.

## New nodes

`def-coef-inserter` defines the inserter of arbitrary parallel functors and its
canonical projection, without accessibility or colimit assumptions, following
Ching--Riehl Appendix A, Definition A.3, printed p. 10. It cites the existing
category node `def-nagata-category`. The three kinds of Mathlib search and the
DAG/upstream/shared-source searches above found no generic inserter definition;
the endofunctor-algebra category is only a specialization. Its module has real
object, morphism and functor data; it is a reusable categorical definition, not
another copy of an accessibility predicate. The main item cites this node in
`stmt_deps` and imports its recorded module. The equifier needs no new node or
private definition because the exact full-subcategory construction already
exists in Mathlib.

## Second reading by Q112

I opened the item node, its recorded dependency declarations, the two delivered modules,
and the Ching--Riehl Appendix A source cited by the node. The item is a statement node;
its Lean theorem has the exact recorded signature (including all universe parameters) and
ends in `:= by sorry`.

The correspondence is as follows. The first conjunct binds an arbitrary small index type
`S : Type w`, a family `A : S → Type u₁`, a `Category.{w}` instance and an
`IsAccessibleCategory.{w}` instance for each factor. It concludes accessibility of the
dependent product `(∀ s, A s)` and accessibility of every `Pi.eval A s`. The second
conjunct binds categories `A` and `B` with independent object universes and `Category.{w}`
instances, parallel functors `F G : A ⥤ B`, accessibility instances for both categories
and both functors, and concludes accessibility of `Inserter F G` and
`Inserter.forget F G`. The third conjunct binds the same category and functor data plus
natural transformations `α β : F ⟶ G`; it concludes accessibility of the full subcategory
`ObjectProperty.FullSubcategory (fun X : A ↦ α.app X = β.app X)` and of its inclusion
`ObjectProperty.ι`. No hypothesis is added, omitted, or strengthened, and each conclusion
uses its own existential cardinal through Mathlib's accessibility classes.

I checked the new dependency node `def-coef-inserter` against Definition A.3. Its
`Inserter` structure has exactly an object `obj : A` and an arrow `hom : F.obj obj ⟶
G.obj obj`; `Inserter.Hom` has an underlying arrow and the commuting equation. The category
instance uses source identities and composition, and `Inserter.forget` is the canonical
projection. The equation is written in the symmetric Lean order
`F.map f ≫ Y.hom = X.hom ≫ G.map f`, which is exactly
`G(f) ∘ u = v ∘ F(f)` under Mathlib's `≫` convention. It has real data throughout and no
hollow definition or private replacement of a recorded notion.

Edge cases were checked against the source and the statement: an empty `S` gives the
terminal product and a vacuous projection family; an empty factor is allowed; empty source,
inserter, and equifier categories are not excluded; `F = G` still leaves arbitrary inserter
endomorphism data; `α = β` gives the whole full subcategory; an empty equifier is allowed;
`ℵ₀` is allowed as an accessibility cardinal; and no zero-object, completeness,
faithfulness, characteristic, or common-cardinal assumption is present. The independent
object universes `u₁`, `u₂` and common Hom universe `w` preserve the node's size convention.

I repeated the existing-definition searches with LeanSearch, Loogle/LeanFinder, `rg` over
Mathlib and `WeilConjectures`, and the shared `lean/Sheaf` tree. They found only generic
accessibility predicates and supporting set-valued limit lemmas, with no generic inserter,
equifier, or PIE-closure declaration. The DAG search likewise contains no prior inserter
definition. The source and Mathlib declarations used by the worker are therefore the
correct ones; no duplicate-definition repair is needed.

No mismatch was found. I changed no Lean statement or node field. Both modules compile
separately with the required `scompile.py` wrapper, with only the expected postponed proof
(`sorry`) and no errors or warnings.

Additional independent checks: `Cardinal.IsRegular` in
`Mathlib/SetTheory/Cardinal/Regular.lean` explicitly includes `aleph0_le` and equality
with cofinality, hence exactly infinite regular cardinals. `IsCardinalFiltered` in
`Presentable/IsCardinalFiltered.lean` quantifies over functors with
`HasCardinalLT (Arrow A) κ`, so the empty test diagram enforces nonemptiness.
`IsCardinalPresentable` in `Presentable/Basic.lean` uses covariant Hom, and
`IsCardinalAccessibleCategory` in `Presentable/LocallyPresentable.lean` extends
`HasCardinalFilteredGenerator` and `HasCardinalFilteredColimits`. The generator property
in `Presentable/CardinalFilteredPresentation.lean` is essentially small and supplies
small filtered presentations, exactly as in the node. Although `Functor.IsAccessible`
only asserts preservation, enlarging its witness to the maximum with a source
accessibility witness supplies the required existence of those colimits; no hypothesis
is lost. The same argument applies to the three output projections after their source
accessibility conjuncts. The colimit dependency is the actual chosen universal colimit
(`Limits/HasLimits.lean`, generated by `to_dual` from `limit`), and the new node's
category dependency is the actual `Category`/`CategoryStruct` interface. Each of the
item's twelve proof steps occurs in its theorem docstring. There is no repair note for
the item and no statement correction or dependency-module repair in this delivery.

Independent search queries and results: LeanFinder, “Accessibility of products and
comma-like categories with a specified arrow F X to G X”, returned eight supporting
accessibility/density results, no match. Loogle `"IsAccessibleCategory"` returned twelve
results (including online comma, arrow, over and under cases), none the three-clause
statement. LeanSearch, “The category of pairs of an object X and a map F X to G X with
commuting squares as morphisms”, returned eight comma/pullback results. `Comma` allows
two independently varying source objects and two independent arrow components, so it
is not the inserter with one object and one arrow component. Direct `rg -n -i
'inserter|equifier|pie.closure'` in the supplied Mathlib CategoryTheory, upstream
WeilConjectures and shared Sheaf trees found only explanatory downstream references in
the latter. The declaration-name index has no proposed-name collision. These checks
independently justify retaining the new inserter construction and the theorem module.

The external source was opened directly at
[Ching--Riehl Appendix A](https://math.jhu.edu/~eriehl/coalgebraic.pdf): printed p. 9
states creation of PIE limits in ACC; p. 10 gives the exact inserter and equifier data;
pp. 10–11 explicitly assert accessibility of the projections; Remark A.4 allows an
increased output rank. I also read the blueprint ancestor's paragraph 2 at the recorded
local path: the categorical input is an auxiliary formalization step, as the node
already records, rather than a verbatim blueprint assertion. No Stacks tag purports to
state this categorical theorem. The new definition node's required fields, source,
three search kinds, category dependency, ancestor/via path, chapter/unit and declaration
list all match the stage-2 extra-node rule.
