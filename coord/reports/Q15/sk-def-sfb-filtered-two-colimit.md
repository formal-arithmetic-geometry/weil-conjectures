## Worker report

The node is already stated by the existing declaration
`CategoryTheory.CategoryCocone.IsFilteredTwoColimit` in
`WeilConjectures.CategoryTheory.FilteredTwoColimit`.
No Lean module is added. The declaration is a `structure ... : Prop` with fields
`essSurjObj`, `homSurj`, and `homInj`.

The recorded dependency declarations are:

- `det-def-sfb-filtered-two-colimit-cocone`: `CategoryTheory.CategoryCocone` in
  `WeilConjectures.CategoryTheory.FilteredTwoColimit`.
- `det-def-sfb-filtered-two-colimit-conditions`:
  `CategoryTheory.CategoryCocone.IsFilteredTwoColimit` in the same module.

The existing structure renders the statement clause by clause. Its
`essSurjObj` field says that for every vertex object `d` there is an index and
stage object whose image is isomorphic to `d` (equivalent to the node's displayed
orientation `d ≅ Φ_i(x)` by symmetry). Its `homSurj` field quantifies over
`i,j,x,y,φ`, supplies `k ≥ i,j` and `g : T_{ik}x ⟶ T_{jk}y`, and states the
comparison-isomorphism formula. Its `homInj` field quantifies over `k,x,y,g,g'`
with equal images and supplies `k' ≥ k` where the transition images are equal.
The upstream `CategoryCocone` fields use exactly the transition functors,
vertex functors, and isomorphisms specified by the cocone dependency; no
coherence or directedness hypothesis is added to this predicate.

Edge cases checked: the preorder index may be empty or nondirected (the
predicate then has the corresponding quantified behavior), singleton indices
are allowed, and zero/empty categories are not excluded. The universes are
those explicitly bound by the upstream declaration.

Searches made:

- `msearch.py ... leanfinder "filtered 2-colimit predicate cocone categories objects morphisms finite stage"`:
  only generic filtered-colimit and eventual-constancy declarations; no exact
  competing predicate.
- `msearch.py ... loogle "CategoryTheory.CategoryCocone.IsFilteredTwoColimit"`:
  unknown identifier in Mathlib, so no Mathlib match.
- `msearch.py ... grep "CategoryCocone|IsFilteredTwoColimit|FilteredTwoColimit"`
  over the source: no duplicate in the slopmaster2 source tree; the current
  server module is the exact existing declaration.
- `scompile.py --source WeilConjectures.CategoryTheory.FilteredTwoColimit`
  printed the current source and verified the full declaration signature and
  docstrings.

## Second reading by Q15

I independently read the sandbox node, its complete source `_section.md` in
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-filtered-two-colimit/`,
the chapter introduction, both statement-dependency nodes and their source pages,
and the complete current `WeilConjectures.CategoryTheory.FilteredTwoColimit` source
returned by `scompile.py --source`. This item cites the blueprint definition,
not a Stacks tag. The chapter's coefficient settings are applications, not
additional hypotheses on this ordinary-category definition. There is no repair
note for this item, no statement correction, no new node, and no dependency module.

Here is my independent inventory and comparison; all verdicts are exact matches.

1. Index: a preordered set, directed only in applications. Lean binds
   `{I : Type w} [Preorder I]`; there is no `IsDirected`, `IsFiltered`,
   `Nonempty`, or `PartialOrder` assumption.
2. Stage categories and vertex: `(C : I → Type u) [∀ i, Category.{v} (C i)]`
   and `(D : Type u') [Category.{v'} D]`. These are arbitrary ordinary categories.
3. Transition functors for each inequality: `CategoryCocone.T` has signature
   `∀ {i j : I}, i ≤ j → (C i ⥤ C j)`.
4. Vertex functors: `CategoryCocone.Φ : ∀ i, C i ⥤ D`.
5. Natural isomorphisms: `CategoryCocone.iso` has signature
   `∀ {i j : I} (h : i ≤ j), T h ⋙ Φ j ≅ Φ i`.
   Its component goes from `Φ_j(T_ij x)` to `Φ_i(x)`, exactly as in the source.
   The structure has just these three fields: no identity, composition,
   normalization, or coherence law is imposed.
6. (Obj): `EssSurjObj` is
   `∀ d : D, ∃ (i : I) (x : C i), Nonempty ((c.Φ i).obj x ≅ d)`.
   `IsFilteredTwoColimit.essSurjObj` asserts this predicate. Reversing the
   displayed isomorphism by symmetry gives precisely the source's orientation;
   `Nonempty` expresses existence of an isomorphism, without choosing data.
7. (Hom-surj): `HomSurj` universally quantifies over `i j`, `x : C i`,
   `y : C j`, and `f : (c.Φ i).obj x ⟶ (c.Φ j).obj y`, in that order. It then
   supplies `k`, `hi : i ≤ k`, `hj : j ≤ k`, and
   `g : (c.T hi).obj x ⟶ (c.T hj).obj y`, with equation
   `f = (c.iso hi).inv.app x ≫ (c.Φ k).map g ≫ (c.iso hj).hom.app y`.
   Lean's left-to-right composition is exactly the source's right-to-left
   formula. `IsFilteredTwoColimit.homSurj` asserts this entire condition.
8. (Hom-inj): `HomInj` quantifies over `k`, `x y : C k`, `g g' : x ⟶ y`,
   and equality `(c.Φ k).map g = (c.Φ k).map g'`; its conclusion is
   `∃ (k' : I) (h : k ≤ k'), (c.T h).map g = (c.T h).map g'`.
   This is exactly the eventual equality demanded, and is asserted by
   `IsFilteredTwoColimit.homInj`.
9. The definition is the conjunction of precisely these three predicates:
   `structure IsFilteredTwoColimit : Prop where` has only the three fields above.
   The node's final finite-stage assertions are also already provided by
   `IsFilteredTwoColimit.exists_iso` and `IsFilteredTwoColimit.exists_map_eq`,
   whose bodies are the corresponding field applications. No additional
   theorem or comparison-category equivalence is part of this definition.

Dependency check: the cocone dependency records exactly the structure inspected
in items 1–5. The conditions dependency records the very same predicate as this
item, and agrees with items 6–9, so using the existing declaration also respects
one definition per notion. No dependency repair is needed. The optional third
proof paragraph of the node explicitly concerns the additional directed,
coherent normalized model; it does not add hypotheses to this predicate. The
upstream module's informal comparison-category discussion is not used as a
claim for arbitrary incoherent transition data.

Edge cases: if `I` is empty, (Obj) holds exactly when `D` is empty and both Hom
conditions are vacuous. If every stage is empty, (Obj) similarly forces the
vertex to be empty. Singleton and nondirected preorders are allowed; where no
common upper bound exists, Hom-surj imposes exactly the source's conditional
existence requirement for each actual arrow. Empty categories, zero objects,
and zero arrows receive no additional restrictions; no additive structure is
assumed. There is no degree, characteristic, scheme, or `n` parameter here.
The five explicit universe variables `w v u v' u'` keep index, stage objects,
stage morphisms, vertex objects, and vertex morphisms independent. No equality
of these universes or smallness instance has been introduced, and all variables
are bound by the surrounding declaration context.

Independent searches, with wording different from the first reader's:

- LeanSearch via `msearch.py`: "ordinary categories indexed by a preorder
  functors to a vertex objects lift up to isomorphism arrows lift and become
  equal at an upper bound". Eight results included
  `Preorder.coconeOfUpperBound`, preorder colimit results, and full/faithful
  `preordToCat`; none defines this predicate on varying categories.
- LeanFinder via `msearch.py`: "joint essential surjectivity of a family of
  functors with eventual fullness and eventual equality of morphisms".
  Eight results included `CategoryTheory.Functor.EssSurj`, comma-category
  essential-surjectivity lemmas, and eventual ranges of Type-valued functors.
  I opened `Functor.EssSurj` in Mathlib: it concerns one functor and provides
  only an object condition, not either Hom condition.
- Direct `rg` on Mathlib CategoryTheory, upstream `WeilConjectures`, and the
  project's `lean/Sheaf` searched `two.?colimit|2.?colimit|bicolimit`,
  joint fullness/faithfulness, and eventual equality/morphisms. I opened
  Mathlib's `JointlyFaithful`: it has a common source and immediate equality,
  unlike these varying sources with eventual equality. Project filtered-site
  modules concern coherent ordinary colimits, not this cocone predicate.
  Exact-name searches across all upstream `WeilConjectures` and `lean/Sheaf`
  found only the project's `PointFdQbarCategory` consumer. The newer current
  framework source, inspected directly and via the prescribed source wrapper,
  supplies the exact existing declaration. No competing definition is needed.

No mathematical or signature mismatch was found; no Lean or node edit was
necessary. The node's `lean.statement`, `structure IsFilteredTwoColimit : Prop`,
is verbatim the existing signature preceding `where`. The source declaration
is a genuine Prop structure and its constituent definitions have explicit
formulae; no hollow data or new proofs are introduced. Existing-source
bindings require no new module or replacement docstrings. This report now
supplies the complete independent clause audit, source review, and searches.
The delivery wrapper will compile an import and `#check` of the existing
binding and run the current server preflight; there are no delivered Lean
files requiring separate compilation.
