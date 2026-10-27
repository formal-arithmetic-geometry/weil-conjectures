## Worker report

`Sheaf.SixFunctors.LevelwiseQuasicoherentBrown` states the two cases of
lem-sfb-levelwise-quasicoherent-brown with three postponed theorems (all proofs
are `by sorry`):

- `CategoryTheory.scheme_quasicoherent_brown` states the single-scheme case,
  independently of any semisimplicial diagram.
- `CategoryTheory.SemisimplicialRingedTotal.exists_schemePresentation` supplies
  the small Zariski realization implicit in the setup of the system case, for
  every semisimplicial scheme. It prevents the presentation data from being an
  unprovided existence hypothesis.
- `CategoryTheory.levelwise_quasicoherent_brown` states the system case, including
  all underived Grothendieck and closure clauses.

The definitions contain actual data. The helper structures and predicates collect
precisely the setup and assertions introduced within this node; they introduce no
independent notion requiring another DAG node. In particular, there is no
identification of D(QCoh) with the full cohomology-constrained subcategory of the
ambient derived category.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Fixed size convention for sites, Hom sets and coproduct indices | Explicit universes `u w a d v`; schemes, small component sites and coproduct indices use `u`. The target may have Hom types in independent `v`, with `[LocallySmall.{u} D]`. The single-scheme localization Hom universe `w` is independent; the total category uses the dependency's `Site.hasDerived` in `u + 1`. |
| Any scheme T | `scheme_quasicoherent_brown (X : Scheme.{u})`; no finiteness, separation or Noetherian binder. |
| Ordinary unbounded derived category of structure-module sheaves | The exact shared carrier `SheafOfModules.{u} (moduleRings X.toRingedSpace)` and `[HasDerivedCategory.{w} ...]`. No bounded subcategory or boundedness predicate is used. |
| Full category of objects with quasi-coherent cohomology | The recorded `schemeDerivedQCohProperty X`, with `.FullSubcategory` inside `OrdinaryQuasiCoherentBrown`. This uses the existing property, not a copy. |
| Small semisimplicial diagram of schemes | `T : SemiSimplexCategoryᵒᵖ ⥤ Scheme.{u}`. The index is the category of finite nonempty ordinals and injective monotone maps. |
| Use the small Zariski ringed sites | `schemeZariskiRingedSite` uses `X.Opens`, `Opens.grothendieckTopology X`, and the actual structure sheaf `X.sheaf`. `SchemePresentation.site_eq` fixes each fibre to this site. |
| The specified transition module pullbacks | `SchemePresentation.pullback` identifies `(P.pullback f).ordinary`, after the component identifications, with `Scheme.Modules.pullback (T.map f)`. These are natural isomorphisms between the actual pullback functors. |
| Exact transition pullbacks | The `exact` binder requires `PreservesFiniteLimits` and `PreservesFiniteColimits` for each `(P.pullback f).ordinary`. The identified scheme pullbacks have the same exactness. |
| Ringed total module category and exact evaluations from the dependency | Parameters `F`, `S`, `R`, `h`, and `P : SemisimplicialRingedTotal.Presentation R h`; the module category is `(R.total h).modules`. All ordinary/derived evaluations are the recorded `P.evaluation` and its `.derived`, with their dependency-supplied exactness. |
| Component identifications are site transport, not arbitrary equivalences of module categories | `SchemePresentation.modules` is normalized by `obj_eq` and `map_eq`: both functor actions are heterogeneously equal to the original object/map. The site equality supplies the change of dependent types. The existence theorem supplies this data for every T. |
| Full underived category A of levelwise quasi-coherent systems | `levelwiseQuasiCoherentProperty P Z` is `∀ i, SheafOfModules.IsQuasicoherent` of the evaluated module, identified with a module on `T.obj i`. Its `.FullSubcategory` is A. The coefficient sheaf is explicitly `(T.obj i).ringCatSheaf`. |
| No invertibility of transitions | Objects are the dependency's actual total modules. Neither the property nor a theorem hypothesis uses `IsCartesian`, `IsIso` on transitions, or a cartesian-system category. |
| Full derived subcategory with every H^q(e_n E) quasi-coherent | `levelwiseDerivedQuasiCoherentProperty P Z` quantifies `i : SemiSimplexCategoryᵒᵖ` and `q : ℤ`, applying `DerivedCategory.homologyFunctor` to `(P.evaluation i).derived.obj E`, then the same normalized component identification and quasi-coherence predicate. Its `.FullSubcategory` is used throughout the Brown assertion. |
| M is Grothendieck abelian | `IsGrothendieckAbelian.{u} (R.total h).modules`; its Abelian instance is the actual sheaf-of-modules instance. |
| A is Grothendieck abelian | `∃ hAb : Abelian (...).FullSubcategory, @IsGrothendieckAbelian.{u} _ _ hAb`; the structure is a conclusion, not a hypothesis. |
| Kernels, cokernels and extensions of A in M stay in A | The three separate `IsClosedUnderKernels`, `IsClosedUnderCokernels` and `IsClosedUnderExtensions` conjuncts for `levelwiseQuasiCoherentProperty P Z`. These are weak-Serre closure conditions; closure under arbitrary subobjects/quotients is not substituted. |
| A is closed under coproducts | `∀ I : Type u, ObjectProperty.IsClosedUnderColimitsOfShape ... (Discrete I)`. This includes the empty family. |
| The full derived categories are ordinary triangulated categories | `OrdinaryQuasiCoherentBrown.triangulated : Q.IsTriangulated` gives Mathlib's induced shift and distinguished triangles on `Q.FullSubcategory`. The ambient derived category is triangulated, so its full triangulated subcategory is triangulated as well. |
| Set-indexed derived coproducts | `OrdinaryQuasiCoherentBrown.coproducts` provides `HasCoproducts.{u} Q.FullSubcategory`; `inclusion_coproducts` states that its full inclusion preserves them. |
| Computed by termwise sheaf coproducts | `termwise_coproducts` takes any family of unbounded cochain representatives whose images lie in Q. The apex of `HomologicalComplex.coconeOfHasColimitEval (Discrete.functor K)` has image in Q, and its image under `DerivedCategory.Q` is a colimit cocone. This fixes the actual degreewise coproduct object, differentials and coprojections, including the empty case. |
| Any locally small triangulated target with coproducts | The target binders `D`, `Category.{v}`, `LocallySmall.{u}`, `Preadditive`, `HasZeroObject`, `HasShift D ℤ`, additive shifts, `Pretriangulated`, `IsTriangulated`, and `HasCoproducts.{u}` in both theorems and the assertion structure. |
| Every exact coproduct-preserving functor | `right_adjoint` quantifies `G : Q.FullSubcategory ⥤ D` with `[G.CommShift ℤ]`, `[G.IsTriangulated]` and `∀ I : Type u, PreservesColimitsOfShape (Discrete I) G`. |
| Ordinary right adjoint | The conclusion `G.IsLeftAdjoint` is Mathlib's assertion that a functor R and an ordinary adjunction G ⊣ R exist. |
| No qcqs or boundedness requirement | Neither theorem has any such binder; evaluations and representatives are unbounded. |

Dependencies read and used:

- `def-weil-size-convention`: metatheoretic convention, with no declaration;
  implemented by the explicit universes described above.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-pc-derived-category`: `WeilConjectures.AlgebraicGeometry.DerivedCategory`,
  `schemeDerivedCategory`, `schemeDerivedQCohProperty` and
  `schemeDerivedQCohCategory`. The shared sheaf-module carrier and category
  instance are retained.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`, which publicly
  exposes the exact Mathlib `SheafOfModules.IsQuasicoherent` predicate. Its
  finite-type/coherence notions are not substituted for quasi-coherence.
- `lem-sfb-semisimplicial-ringed-total-category`:
  `Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory`, its `Site`,
  `RingDiagram`, `RingDiagram.total`, `Presentation`, `Evaluation.ordinary`,
  `Evaluation.derived` and `Presentation.pullback`. The full module, including
  its source docstrings and theorem signature, was read.
- `def-sp-grothendieck-abelian`: Mathlib's `IsGrothendieckAbelian` at size `u`,
  with its AB5, generator and local-smallness fields.
- `def-weil-triangulated-category`: Mathlib's `Pretriangulated`,
  `IsTriangulated`, and `Functor.IsTriangulated`, together with `CommShift`.

All currently recorded proof-dependency modules are imported (the node
`lem-sfb-grothendieck-weak-serre-derived-representability` currently has no
recorded Lean declaration and hence no module to import). The proof docstrings
carry every step of the node's proof, including component generators, exact
free evaluations, componentwise AB5, weak-Serre closure, cohomological Brown and
Yoneda assembly. The realization theorem's docstring also explains the Zariski
specialization of the recorded total-category construction.

Edge cases checked: the empty scheme and zero module category; empty and
infinite coproduct families; zero or arbitrary noninvertible transitions;
unbounded complexes with nonzero cohomology in arbitrarily large positive or
negative degrees; schemes which are neither quasi-compact nor quasi-separated;
target Hom types in an independent universe admitting the specified small model.
The source categories remain full subcategories of the ambient derived category,
including when D(QCoh) would be a different category. No extra equality of site,
module and localization Hom universes is imposed.

Searches made before introducing the declarations:

- `msearch.py leanfinder`: “For an arbitrary scheme or a semisimplicial diagram
  with exact pullbacks, exact coproduct preserving functors on the derived
  category with quasi coherent cohomology have right adjoints”. Eight hits were
  underived sheaf/module adjunctions; none states this result.
- `msearch.py leansearch`: “The derived category of a weak Serre Grothendieck
  subcategory closed under coproducts has Brown representability”. Eight hits
  concern the ambient localization, Ext or Serre-class closure, not this theorem.
- `msearch.py loogle`: `Functor.IsRightAdjoint, PreservesCoproductsOfSize,
  IsTriangulated`. Zero hits, with the unknown-identifier diagnostic for the
  first name. The actual ordinary-adjoint interface was then read from
  Mathlib's Adjunction/Basic.lean.
- `msearch.py grep`: `Brown|[bB]rown|[rR]epresentab` under
  `CategoryTheory/Triangulated`: only a bibliography reference in
  `Generators.lean`.
- `rg` over the project and upstream for `Brown|brown|levelwiseQuasi|levelwise_quasi`
  found general compact-generation and ambient Grothendieck Brown results, which
  do not state Brown for the quasi-coherent full derived subcategory. In
  particular `DerivedCategory.isLeftAdjoint_of_preservesCoproducts` concerns
  D(A), not D_QCoh(M). No declaration already gives this node.
- `grep -rn 'lem-sfb-levelwise-quasicoherent-brown' lean/WeilConjectures` found
  no match. Exact-name searches over both libraries and the DAG found none of
  the new helper names. The module reuses, rather than duplicates, the recorded
  site/system, derived-category and quasi-coherence definitions.

Source checks: read Stacks 077P and 0D72 in the local source and at their tag
pages, HNR arXiv:1405.1888v2 Appendix A Theorem A.3 and Appendix B Theorem B.1
at https://arxiv.org/html/1405.1888, and the current blueprint unit's direct-image
proof in literature/blueprint/latest. The HNR theorem uses a coproduct-closed
weak Serre Grothendieck subcategory, as required; no Serre hypothesis is added.
No node statement was corrected and no dispute remains.

## Second reading by Q01

This is a second semantic pass by the same worker; the dispatch brief prohibits
starting another agent and reserves the independent review to the maintainer.
I reread the node and final module together. An ambient-derived-category draft
was rejected during this pass and replaced: the final assertions use the actual
full quasi-coherent derived subcategories, assert their coproduct existence, and
retain all underived closure and Grothendieck conclusions. The single-scheme
case is now a separate theorem, so it cannot depend on diagram presentation
existence. The explicit Zariski realization theorem supplies that presentation
for every semisimplicial scheme. Its identity-on-objects/maps normalization rules
out choosing an arbitrary equivalence to define quasi-coherence.

I checked that both quasi-coherence predicates explicitly use the structure ring
of the correct component, that every degree and component is quantified, and
that no system transition is inverted. I checked the induced source
triangulation against Mathlib's full-subcategory instance, and read the
`OrdinaryQuasiCoherentBrown` fields against every coproduct and right-adjoint
clause. The termwise clause uses the actual degreewise cocone, not an arbitrary
isomorphism between candidate objects. The target is triangulated (including
TR4), exactness includes commutation with integer shifts, and the adjoint is an
ordinary categorical adjoint. Every non-proof definition has real data and each
postponed theorem has this node's blueprint tag and a natural-language proof.
