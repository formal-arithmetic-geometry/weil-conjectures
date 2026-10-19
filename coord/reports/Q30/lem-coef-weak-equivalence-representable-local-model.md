## Worker report

The module `Sheaf.CategoryTheory.WeakEquivalenceRepresentableLocalModel` states
`HomotopicalAlgebra.WeakRepresentable.weak_equivalence_representable_local_model`.
It has one postponed theorem, with the complete eight-step DAG proof in its docstring.
The other declarations construct or package this node's canonical maps and comparison;
no construction is chosen from an undetermined existence theorem.

The statement and source of the item are unchanged. I opened HAG II at the recorded URL,
Appendix A, printed pp. 208–209: the paragraph following A.0.3 identifies the local
representable model, its equivalence mapping spaces and its derived slice maps; p. 209
explicitly discusses obtaining functoriality by simplicial localization. The PDF's
zero-based page is 214 for printed p. 208. No source correction is needed.

Each hypothesis and clause is rendered as follows.

| Node clause | Lean rendering |
| --- | --- |
| Model category, complete and cocomplete | `M`, `[Category.{v} M]`, `[HasLimits M]`, `[HasColimits M]`, `[ModelCategory M]` |
| Both functorial model factorizations | The two `HasFunctorialFactorization` instances for cofibrations/trivial fibrations and trivial cofibrations/fibrations |
| Given homotopy coherent localization q | `q : FiniteReedy.largeNerve M ⟶ K` and `hq : FiniteReedy.IsLocalization (weakEquivalences M) q` |
| Full subcategory U, closed in both directions | `P : ObjectProperty M` and `hP`, with equivalence `P X ↔ P Y` for every weak arrow |
| C has precisely U's objects and actual weak arrows | `InducedWideCategory M (fun X : P.FullSubcategory ↦ X.obj) (weakEquivalences M)` |
| Enlarge universes to make C small | `AsSmall.{t}`; its objects and arrows both lie in `max u v t`, without identifying u and v |
| h_x(y) is the discrete set of actual weak arrows | `representables C`, definitionally the functor of existing `SSet.ProjectivePresheaf.representable x`; objects are ordinary `yoneda` followed by the constant simplicial-set functor |
| Use P_lc(C) from the slice dependency | The existential `p : SSet.LocallyConstantPresheafSlice.Presentation C`, with its recorded localized model structure |
| A fibrant E_x for every x | `(localHom enriched arrows).obj x`, and `LocalModel.fibrant` |
| Actual local weak equivalence h_x → E_x | `LocalModel.unit.app x` and `LocalModel.local_equivalence` |
| Mapping-into-local-Kan meaning of local equivalence | `p.localized_weak` identifies its weak class with `BousfieldLocalization.localEquivalences` for the representable arrows; `p.localized_fibrant` identifies fibrant tests with objectwise Kan arrow-inverting presheaves |
| Values E_x(y) | Definitionally `CoherentNerve.hom enriched (arrows.obj y) (arrows.obj x)` by `localHom`, using Mathlib's `eHomFunctor` |
| Equivalence components of Map(qy,qx) | The existing `Enhanced.fullSubcomplex` of `Enhanced.mappingSpace K` selected by `Enhanced.IsEquivalenceEdge`; `objects` identifies its endpoints with the images under q |
| Weak homotopy equivalences of values | `LocalModel.value` and `LocalModel.value_weak` |
| Comparison on actual weak equivalences is induced by q | `unit_formula` identifies each actual arrow's unit image with `eHomEquiv` of `arrows.map f`, and `actual_arrows` identifies its value comparison with `d` applied to `ComposableArrows.mk₁ f`; `d` is `restrictedLocalization P q` |
| Naturality contravariantly in y and covariantly in weak x | `localHom` is the actual restricted enriched Hom bifunctor, and `unit` is a natural transformation of C-indexed presheaves |
| Composition and higher homotopies | One `comparison : nerveFunctor.obj enriched ⟶ K`, rather than separate pairwise maps. `ordinary_normalization` fixes the ordinary-to-coherent nerve map on every simplex. `under_localization` fixes its composite with q on every simplex. `value_formula` identifies the SAME value maps with the existing canonical coherent-nerve mapping comparison followed by `mappingSpaceMap comparison`. The canonical comparison's full-simplex formulas and the single simplicial functor preserve all higher composition data. |
| Identify maps between localized representables with maps induced by q | The unit local equivalences identify these representables with the restricted enriched Hom presheaves. Enriched Yoneda, normalized by `unit_formula` at the identity, identifies composition with the enriched composition; `value_formula` and `actual_arrows` then identify its entire coherent comparison with q. |
| No enrichment, properness or combinatoriality assumed on M | None occurs among the theorem binders. The enriched presentation is existential conclusion data for the localized representables. |

The helpers are part of this node's own comparison, not new independent notions.
`representables` packages existing discrete representables into their canonical functor.
`weakInclusion` is the existing `AsSmall.down` followed by `wideInducedFunctor`.
`restrictedLocalization` applies this inclusion to actual strings and then q.
`localHom` uses the existing enriched Hom bifunctor. `LocalModel` only packages the
required witnesses, equations and properties in the theorem conclusion. In particular,
there is no arbitrary-map hypothesis or hollow Nonempty choice defining an object.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CosimplicialFrameMapping`:
  `CategoryTheory.cosimplicial_frame_mapping`, its model/factorization convention,
  and `HomotopicalAlgebra.FiniteReedy.IsLocalization` and `largeNerve`.
- `Sheaf.CategoryTheory.LocallyConstantPresheafSlice`:
  `SSet.LocallyConstantPresheafSlice.locally_constant_presheaf_slice` and
  `Presentation`, including its `localized_weak`, `localized_fibrant`, enriched
  comparison and evaluation signatures and docstrings.
- Already recorded `lem-coef-coherent-nerve-comparison`, added to stmt_deps:
  `Sheaf.CategoryTheory.CoherentNerveComparison`,
  `CategoryTheory.CoherentNerveComparisonStatement`, its `vertex` and canonical
  `mapping_space_comparison`, and `CategoryTheory.coherent_nerve_comparison`.
  This supplies the existing canonical mapping comparison, not a private copy.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`, inherited through the dependencies:
  `SSet.Enhanced.fullSubcomplex`, `mappingSpace`, `mappingSpaceMap`,
  `IsEquivalenceEdge`, `IsWeakHomotopyEquivalence`.
- `CategoryTheory.SimplicialModelLocalization.IsOrdinaryNerveMap`, inherited from
  `Sheaf.CategoryTheory.SimplicialModelNerveLocalization`: I read its full simplex
  formula. The ordinary map here is normalized by applying that predicate after
  the existing degreewise ULift functor.
- Mathlib's `InducedWideCategory`, `wideInducedFunctor`, `AsSmall.down`, `yoneda`,
  `Functor.const`, `eHomFunctor`, and `eHomEquiv` supply the actual data.
- The existing space-valued straightening dependency is included only to repair
  its compilation through the mandatory slice import; see Dependency modules.

All already stated proof dependencies are imported non-publicly, including the
Mathlib lifting-property module for the mathlib leaf. No proof imports were omitted.
A DFS verified that neither added dependency reaches the item; the path to the repaired
module already exists through locally-constant-presheaf-slice, presheaf-localization,
complete-algebroid and kan-relative-nerve-left-fibration. In particular the downstream
`ModelWeakEquivalenceNerve` theorem is not imported or used. Its helper for equivalence
components is expressed here directly by the same existing `fullSubcomplex` operation,
not defined a second time and not used to introduce a cyclic import.

Edge cases checked before writing and on rereading: P empty (there is no Nonempty
assumption); identity arrows and their degeneracies; isomorphisms as the only weak
arrows, where the comparison reduces to discrete isomorphism sets; non-equivalent
endpoints, where both spaces have no components; arbitrary objects which are neither
cofibrant nor fibrant; all degrees including zero; independent model object and
morphism universes. The Hom presheaf takes its variance from `eHomFunctor`, with the
flip giving x covariant and y contravariant. Identity normalization of the unit ensures
that enriched composition computes the derived Yoneda composition, rather than merely
some composition on weakly equivalent spaces.

Searches for an existing statement:

- `msearch.py`, leanfinder: “Fibrant replacement of a weak-equivalence representable
  on a model category is the derived equivalence mapping presheaf”: eight hits for
  ordinary cofibrant-object homotopy relations, bifibrant inclusions and localization
  morphisms. I read the Bifibrant and CofibrantObjectHomotopy signatures/docstrings;
  they do not state the local simplicial-presheaf theorem.
- `msearch.py`, loogle: `"ModelCategory", "yoneda"`: zero hits.
- `msearch.py`, grep: `fibrant.*representable|equivalence.*mapping.*space`, under
  Mathlib AlgebraicTopology: zero hits.
- `rg` in upstream WeilConjectures and side Sheaf for
  `weakEquivalence.*[Rr]epresentable|representable.*[Ll]ocal[Mm]odel|weak-equivalence-representable-local-model`:
  upstream zero hits; the side result is only the downstream ModelWeakEquivalenceNerve
  proof mentioning the current DAG node. Its statement is the nerve/core comparison,
  not the local representable theorem; no existing declaration states this item.
- Checked `dag/lean_names_upstream.json`, Mathlib, WeilConjectures and Sheaf for
  the new fully qualified names. No collision; the unrelated projective-space
  `localHom` helpers lie in different namespaces.

No STATEMENT-DISPUTED flag and no statement correction. Every definition has actual
construction data; the main theorem alone has a new sorry. The dependency theorem
retains its original sorry and proof plan without adding any postponed fact.

## Dependency modules

`lem-coef-space-valued-straightening`, module
`Sheaf.CategoryTheory.SpaceValuedStraightening`, is an existing transitive dependency
of the required locally constant slice module. The first prescribed compile stopped
in its `Diagrams` abbreviation with `lean.dependsOnNoncomputable`: the published
`smallSpaces` is now noncomputable. I read the current server source with
`scompile.py --source`, copied it into the sandbox, and changed only
`abbrev Diagrams` to `noncomputable abbrev Diagrams`. All data and mathematical
statements, all of its declaration signatures, its theorem and complete proof docstring
are otherwise exactly the current published source. Its node changes only in `lean`,
with a note explaining this §1(B) repair. The item cites the already recorded node so
that its dependency module can be delivered. No other node is edited.

Validation: the prescribed `scompile.py` compiled both delivered files separately,
with the dependency first and the private side overlay. The final run passed preliminary,
sandbox and library confirmation compiles with no errors or warnings. The repaired
dependency compiled in 2.8 seconds and the item in 2.5 seconds in that confirmation.
All lines are at most 100 characters, auto-implicits are disabled, and the JSON records
contain the verbatim final theorem signatures. A parsed field comparison confirmed
that the item changes only in `lean` and added `stmt_deps`, and the dependency node
only in `lean`.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
